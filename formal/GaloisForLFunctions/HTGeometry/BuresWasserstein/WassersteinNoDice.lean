import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinBlockField
import Mathlib.Analysis.PSeries

/-!
# The no-dice theorem

A cyclic (incremental) resolvent iteration visits each single-index field `Ψ_i` once per block of
`m` steps.  Over one block the increments telescope, and replacing every step size `h_j` by the
step size `h_0` at the start of the block and every argument `s_{n₀+j}` by `s_{n₀}` costs only
`O(h_0²)`, because `h_0 - h_j ≤ m h_0²` and the within-block drift is `O(h_0)`.  Since
`∑_i Ψ_i = mΦ`, one block is therefore an explicit Euler step for `Φ` with step `m h_0` and error
`O(h_0²)`.  The Robbins–Monro convergence of the block sequence then transfers to the whole
sequence because the within-block drift tends to zero.
-/

open scoped NNReal Ring BigOperators
open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- Every index beyond the start of the iteration belongs to the index set. -/
lemma idx_mem_of_bijOn {m N₀ : ℕ} (hm : 0 < m) {idx : ℕ → ι}
    (hbij : ∀ k : ℕ, Set.BijOn (fun j => idx (N₀ + k * m + j))
      (↑(Finset.range m)) (↑s : Set ι)) {n : ℕ} (hn : N₀ ≤ n) : idx n ∈ s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hdm : d = m * (d / m) + d % m := (Nat.div_add_mod d m).symm
  have hlt : d % m < m := Nat.mod_lt _ hm
  have hid : N₀ + d = N₀ + (d / m) * m + d % m := by
    rw [Nat.mul_comm (d / m) m]
    omega
  rw [hid]
  have := (hbij (d / m)).mapsTo (by
    simp only [Finset.coe_range, Set.mem_Iio]
    exact hlt)
  exact this

/-- The harmonic step sizes inside one block differ by at most `m h₀²`. -/
lemma one_div_sub_one_div_le {a j mm : ℝ} (ha : 0 ≤ a) (hj : 0 ≤ j) (hjm : j ≤ mm) :
    1 / (a + 1) - 1 / (a + j + 1) ≤ mm * (1 / (a + 1)) ^ 2 := by
  have h1 : (0 : ℝ) < a + 1 := by linarith
  have h2 : (0 : ℝ) < a + j + 1 := by linarith
  rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2), div_pow, one_pow, mul_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hmm : (0 : ℝ) ≤ mm := le_trans hj hjm
  nlinarith [mul_le_mul_of_nonneg_right hjm (sq_nonneg (a + 1)),
    mul_nonneg hmm (mul_nonneg h1.le hj), sq_nonneg (a + 1)]

set_option maxHeartbeats 1000000 in
/-- **Theorem 4.16 (Kim–Mer–Pálfia), the no-dice theorem, in the Hilbert–Schmidt metric.**
A cyclic resolvent iteration with harmonic step sizes converges to the Wasserstein mean. -/
theorem tendsto_noDice {α β Cr : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1))
    {m N₀ : ℕ} (hm : 0 < m) {idx : ℕ → ι}
    {seq : ℕ → E →L[ℂ] E} {Xstar : E →L[ℂ] E}
    (hXstarW : IsWassersteinPoint s w Av Xstar)
    (hXstarα : α • (1 : E →L[ℂ] E) ≤ Xstar) (hXstarβ : Xstar ≤ β • (1 : E →L[ℂ] E))
    (hseqpos : ∀ n, IsStrictlyPositive (seq n))
    (hseqa : ∀ n, α • (1 : E →L[ℂ] E) ≤ seq n)
    (hseqb : ∀ n, seq n ≤ β • (1 : E →L[ℂ] E))
    (hseqHS : ∀ n, IsHilbertSchmidt (seq n - Xstar))
    (hCr : 0 ≤ Cr)
    (hstep : ∀ n, N₀ ≤ n → hsNorm (seq (n + 1)
      - (seq n - (1 / ((n : ℝ) + 1)) • wassPsi (m : ℝ) w Av (idx n) (seq n)))
        ≤ Cr * (1 / ((n : ℝ) + 1)) ^ 2)
    (hbij : ∀ k : ℕ, Set.BijOn (fun j => idx (N₀ + k * m + j))
      (↑(Finset.range m)) (↑s : Set ι)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → hsNorm (seq n - Xstar) < ε := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  -- constants
  obtain ⟨L, hLdef⟩ : ∃ l : ℝ, l = gmFieldLipConst α β := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; exact gmFieldLipConst_nonneg hα hβ
  obtain ⟨Wm, hWdef⟩ : ∃ x : ℝ, x = ∑ i ∈ s, |(m : ℝ) * w i| := ⟨_, rfl⟩
  have hW0 : 0 ≤ Wm := by
    rw [hWdef]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hWi : ∀ i ∈ s, |(m : ℝ) * w i| ≤ Wm := by
    intro i hi
    rw [hWdef]
    exact Finset.single_le_sum (f := fun j => |(m : ℝ) * w j|) (fun j _ => abs_nonneg _) hi
  obtain ⟨Sstar, hSdef⟩ : ∃ x : ℝ, x = ∑ i ∈ s, hsNorm (Xstar - Av i) := ⟨_, rfl⟩
  have hS0 : 0 ≤ Sstar := by
    rw [hSdef]; exact Finset.sum_nonneg fun i _ => hsNorm_nonneg _
  have hSi : ∀ i ∈ s, hsNorm (Xstar - Av i) ≤ Sstar := by
    intro i hi
    rw [hSdef]
    exact Finset.single_le_sum (f := fun j => hsNorm (Xstar - Av j))
      (fun j _ => hsNorm_nonneg _) hi
  -- Hilbert–Schmidt structure
  have hXstar1 : IsHilbertSchmidt (Xstar - 1) :=
    isHilbertSchmidt_sub_one_of_isWassersteinPoint hα hwsum hA hAα hXstarα hAHS hXstarW
  have hXA : ∀ i ∈ s, IsHilbertSchmidt (Xstar - Av i) := by
    intro i hi
    have hid : Xstar - Av i = (Xstar - 1) - (Av i - 1) := by abel_nf
    rw [hid]
    exact hXstar1.sub (hAHS i hi)
  have hseqA : ∀ n, ∀ i ∈ s, IsHilbertSchmidt (seq n - Av i) := by
    intro n i hi
    have hid : seq n - Av i = (seq n - Xstar) + (Xstar - Av i) := by abel_nf
    rw [hid]
    exact (hseqHS n).add (hXA i hi)
  have hseqsub : ∀ n n', IsHilbertSchmidt (seq n - seq n') := by
    intro n n'
    have hid : seq n - seq n' = (seq n - Xstar) - (seq n' - Xstar) := by abel_nf
    rw [hid]
    exact (hseqHS n).sub (hseqHS n')
  have hΨzero : ∀ i ∈ s, wassPsi (m : ℝ) w Av i (Av i) = 0 := by
    intro i hi
    unfold wassPsi
    rw [gm_ringInverse_self' (hA i hi), sub_self, smul_zero]
  have hΨHS : ∀ n, ∀ i ∈ s, IsHilbertSchmidt (wassPsi (m : ℝ) w Av i (seq n)) := by
    intro n i hi
    have h := isHilbertSchmidt_wassPsi_sub (m := (m : ℝ)) (w := w) hi hα hβ hA
      (hseqpos n) (hA i hi) hAα hAβ (hseqb n) (hAβ i hi) (hseqA n i hi)
    rwa [hΨzero i hi, sub_zero] at h
  have hΨlip : ∀ n n', ∀ i ∈ s,
      hsNorm (wassPsi (m : ℝ) w Av i (seq n) - wassPsi (m : ℝ) w Av i (seq n'))
        ≤ (Wm * L) * hsNorm (seq n - seq n') := by
    intro n n' i hi
    have h := hsNorm_wassPsi_sub_le (m := (m : ℝ)) (w := w) hi hα hαβ hA
      (hseqpos n) (hseqpos n') hAα hAβ (hseqa n) (hseqb n) (hseqa n') (hseqb n')
      (hseqsub n n')
    refine h.trans ?_
    rw [← hLdef] at *
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hWi i hi) hL0) (hsNorm_nonneg _)
  have hΨbd : ∀ n, ∀ i ∈ s, hsNorm (wassPsi (m : ℝ) w Av i (seq n))
      ≤ (Wm * L) * (hsNorm (seq n - Xstar) + Sstar) := by
    intro n i hi
    have h := hsNorm_wassPsi_sub_le (m := (m : ℝ)) (w := w) hi hα hαβ hA
      (hseqpos n) (hA i hi) hAα hAβ (hseqa n) (hseqb n) (hAα i hi) (hAβ i hi)
      (hseqA n i hi)
    rw [hΨzero i hi, sub_zero] at h
    refine h.trans ?_
    rw [← hLdef] at *
    have hdist : hsNorm (seq n - Av i) ≤ hsNorm (seq n - Xstar) + Sstar := by
      have hid : seq n - Av i = (seq n - Xstar) + (Xstar - Av i) := by abel_nf
      rw [hid]
      exact (hsNorm_add_le (hseqHS n) (hXA i hi)).trans
        (add_le_add_right (hSi i hi) _)
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hWi i hi) hL0) (hsNorm_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left hdist (by positivity)
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, x = Wm * L := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  -- the per-step drift
  have hdrift : ∀ n, N₀ ≤ n → hsNorm (seq (n + 1) - seq n)
      ≤ (1 / ((n : ℝ) + 1)) * hsNorm (wassPsi (m : ℝ) w Av (idx n) (seq n))
        + Cr * (1 / ((n : ℝ) + 1)) ^ 2 := by
    intro n hn
    have hidx := idx_mem_of_bijOn (s := s) hm hbij hn
    have hΨ := hΨHS n (idx n) hidx
    have hHS1 : IsHilbertSchmidt (seq (n + 1)
        - (seq n - (1 / ((n : ℝ) + 1)) • wassPsi (m : ℝ) w Av (idx n) (seq n))) := by
      have hid2 : seq (n + 1)
          - (seq n - (1 / ((n : ℝ) + 1)) • wassPsi (m : ℝ) w Av (idx n) (seq n))
          = (seq (n + 1) - seq n)
            + (1 / ((n : ℝ) + 1)) • wassPsi (m : ℝ) w Av (idx n) (seq n) := by abel_nf
      rw [hid2]
      exact (hseqsub (n + 1) n).add (hΨ.real_smul _)
    have hid : seq (n + 1) - seq n
        = (seq (n + 1)
            - (seq n - (1 / ((n : ℝ) + 1)) • wassPsi (m : ℝ) w Av (idx n) (seq n)))
          + (-((1 / ((n : ℝ) + 1)) • wassPsi (m : ℝ) w Av (idx n) (seq n))) := by abel_nf
    rw [hid]
    refine (hsNorm_add_le hHS1 ((hΨ.real_smul _).neg)).trans ?_
    rw [hsNorm_neg', hsNorm_real_smul, abs_of_nonneg (by positivity)]
    linarith [hstep n hn]
  -- a crude Gronwall bound inside a block
  have hcrude : ∀ n₀, N₀ ≤ n₀ → ∀ j : ℕ,
      hsNorm (seq (n₀ + j) - Xstar) + Sstar + Cr
        ≤ (2 + K) ^ j * (hsNorm (seq n₀ - Xstar) + Sstar + Cr) := by
    intro n₀ hn₀ j
    induction j with
    | zero => simp
    | succ j ih =>
        have hnj : N₀ ≤ n₀ + j := le_trans hn₀ (Nat.le_add_right _ _)
        have hidx := idx_mem_of_bijOn (s := s) hm hbij hnj
        have hh1 : (1 / (((n₀ + j : ℕ) : ℝ) + 1)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ ((n₀ + j : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have hh0 : (0 : ℝ) ≤ 1 / (((n₀ + j : ℕ) : ℝ) + 1) := by positivity
        have hstepj := hdrift (n₀ + j) hnj
        have hbdj := hΨbd (n₀ + j) (idx (n₀ + j)) hidx
        rw [← hKdef] at hbdj
        have htri : hsNorm (seq (n₀ + (j + 1)) - Xstar)
            ≤ hsNorm (seq (n₀ + j) - Xstar) + hsNorm (seq (n₀ + j + 1) - seq (n₀ + j)) := by
          have hid : seq (n₀ + (j + 1)) - Xstar
              = (seq (n₀ + j) - Xstar) + (seq (n₀ + j + 1) - seq (n₀ + j)) := by
            rw [show n₀ + (j + 1) = n₀ + j + 1 by ring]
            abel_nf
          rw [hid]
          exact hsNorm_add_le (hseqHS (n₀ + j)) (hseqsub (n₀ + j + 1) (n₀ + j))
        have hdn : (0 : ℝ) ≤ hsNorm (seq (n₀ + j) - Xstar) := hsNorm_nonneg _
        have hKS : (0 : ℝ) ≤ K * (hsNorm (seq (n₀ + j) - Xstar) + Sstar) :=
          mul_nonneg hK0 (by linarith)
        have hA1 : (1 / (((n₀ + j : ℕ) : ℝ) + 1))
            * hsNorm (wassPsi (m : ℝ) w Av (idx (n₀ + j)) (seq (n₀ + j)))
            ≤ 1 * (K * (hsNorm (seq (n₀ + j) - Xstar) + Sstar)) :=
          mul_le_mul hh1 hbdj (hsNorm_nonneg _) zero_le_one
        have hA2 : Cr * (1 / (((n₀ + j : ℕ) : ℝ) + 1)) ^ 2 ≤ Cr := by
          have hsq : (1 / (((n₀ + j : ℕ) : ℝ) + 1)) ^ 2 ≤ 1 := by
            rw [sq]
            nlinarith [hh1, hh0]
          nlinarith [hsq, hCr]
        have hstep2 : hsNorm (seq (n₀ + j + 1) - seq (n₀ + j))
            ≤ K * (hsNorm (seq (n₀ + j) - Xstar) + Sstar) + Cr := by
          linarith [hstepj, hA1, hA2]
        have hgrow : hsNorm (seq (n₀ + (j + 1)) - Xstar) + Sstar + Cr
            ≤ (2 + K) * (hsNorm (seq (n₀ + j) - Xstar) + Sstar + Cr) := by
          nlinarith [htri, hstep2, hdn, hK0, hCr, hS0, mul_nonneg hK0 hCr]
        have hpow : (0 : ℝ) < (2 + K) := by linarith
        calc hsNorm (seq (n₀ + (j + 1)) - Xstar) + Sstar + Cr
            ≤ (2 + K) * (hsNorm (seq (n₀ + j) - Xstar) + Sstar + Cr) := hgrow
          _ ≤ (2 + K) * ((2 + K) ^ j * (hsNorm (seq n₀ - Xstar) + Sstar + Cr)) :=
              mul_le_mul_of_nonneg_left ih hpow.le
          _ = (2 + K) ^ (j + 1) * (hsNorm (seq n₀ - Xstar) + Sstar + Cr) := by ring
  -- the within-block drift
  have hQ : ∀ n₀, N₀ ≤ n₀ → ∀ j : ℕ, j ≤ m →
      hsNorm (seq (n₀ + j) - seq n₀)
        ≤ (j : ℝ) * ((1 / ((n₀ : ℝ) + 1))
          * (K * ((2 + K) ^ m * (hsNorm (seq n₀ - Xstar) + Sstar + Cr)) + Cr)) := by
    intro n₀ hn₀ j
    induction j with
    | zero =>
        intro _
        rw [Nat.add_zero, sub_self, hsNorm_zero, Nat.cast_zero, zero_mul]
    | succ j ih =>
        intro hjm
        have hj : j ≤ m := le_trans (Nat.le_succ j) hjm
        have ihj := ih hj
        have hnj : N₀ ≤ n₀ + j := le_trans hn₀ (Nat.le_add_right _ _)
        have hidx := idx_mem_of_bijOn (s := s) hm hbij hnj
        have hstepj := hdrift (n₀ + j) hnj
        have hbdj := hΨbd (n₀ + j) (idx (n₀ + j)) hidx
        rw [← hKdef] at hbdj
        have hhle : (1 / (((n₀ + j : ℕ) : ℝ) + 1)) ≤ 1 / ((n₀ : ℝ) + 1) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          push_cast
          have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
          linarith
        have hh0 : (0 : ℝ) ≤ 1 / (((n₀ + j : ℕ) : ℝ) + 1) := by positivity
        have hh01 : (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) := by positivity
        have hh1 : (1 / ((n₀ : ℝ) + 1)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
          linarith
        have hpowle : (2 + K) ^ j ≤ (2 + K) ^ m := by
          refine pow_le_pow_right₀ (by linarith) hj
        have hDS : (0 : ℝ) ≤ hsNorm (seq n₀ - Xstar) + Sstar + Cr := by
          have := hsNorm_nonneg (seq n₀ - Xstar); linarith
        have hcr := hcrude n₀ hn₀ j
        have hbig : K * (hsNorm (seq (n₀ + j) - Xstar) + Sstar)
            ≤ K * ((2 + K) ^ m * (hsNorm (seq n₀ - Xstar) + Sstar + Cr)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          have h1 : hsNorm (seq (n₀ + j) - Xstar) + Sstar
              ≤ (2 + K) ^ j * (hsNorm (seq n₀ - Xstar) + Sstar + Cr) := by linarith [hcr, hCr]
          exact h1.trans (mul_le_mul_of_nonneg_right hpowle hDS)
        have hΨnn : (0 : ℝ) ≤ hsNorm (wassPsi (m : ℝ) w Av (idx (n₀ + j)) (seq (n₀ + j))) :=
          hsNorm_nonneg _
        have hone : hsNorm (seq (n₀ + j + 1) - seq (n₀ + j))
            ≤ (1 / ((n₀ : ℝ) + 1))
              * (K * ((2 + K) ^ m * (hsNorm (seq n₀ - Xstar) + Sstar + Cr)) + Cr) := by
          have hA1 : (1 / (((n₀ + j : ℕ) : ℝ) + 1))
              * hsNorm (wassPsi (m : ℝ) w Av (idx (n₀ + j)) (seq (n₀ + j)))
              ≤ (1 / ((n₀ : ℝ) + 1))
                * (K * ((2 + K) ^ m * (hsNorm (seq n₀ - Xstar) + Sstar + Cr))) :=
            mul_le_mul hhle (hbdj.trans hbig) hΨnn hh01.le
          have hA2 : Cr * (1 / (((n₀ + j : ℕ) : ℝ) + 1)) ^ 2
              ≤ (1 / ((n₀ : ℝ) + 1)) * Cr := by
            have hsq : (1 / (((n₀ + j : ℕ) : ℝ) + 1)) ^ 2
                ≤ (1 / ((n₀ : ℝ) + 1)) * 1 := by
              rw [sq]
              exact mul_le_mul hhle (le_trans hhle hh1) hh0 hh01.le
            nlinarith [hsq, hCr]
          linarith [hstepj, hA1, hA2]
        have htri : hsNorm (seq (n₀ + (j + 1)) - seq n₀)
            ≤ hsNorm (seq (n₀ + j) - seq n₀) + hsNorm (seq (n₀ + j + 1) - seq (n₀ + j)) := by
          have hid : seq (n₀ + (j + 1)) - seq n₀
              = (seq (n₀ + j) - seq n₀) + (seq (n₀ + j + 1) - seq (n₀ + j)) := by
            rw [show n₀ + (j + 1) = n₀ + j + 1 by ring]
            abel_nf
          rw [hid]
          exact hsNorm_add_le (hseqsub (n₀ + j) n₀) (hseqsub (n₀ + j + 1) (n₀ + j))
        have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hexp : ((j : ℝ) + 1) * ((1 / ((n₀ : ℝ) + 1))
              * (K * ((2 + K) ^ m * (hsNorm (seq n₀ - Xstar) + Sstar + Cr)) + Cr))
            = (j : ℝ) * ((1 / ((n₀ : ℝ) + 1))
              * (K * ((2 + K) ^ m * (hsNorm (seq n₀ - Xstar) + Sstar + Cr)) + Cr))
              + (1 / ((n₀ : ℝ) + 1))
                * (K * ((2 + K) ^ m * (hsNorm (seq n₀ - Xstar) + Sstar + Cr)) + Cr) := by ring
        rw [hexp]
        linarith [htri, ihj, hone]
  -- one block is an explicit Euler step
  have hblockid : ∀ k : ℕ,
      seq (N₀ + k * m + m) - (seq (N₀ + k * m)
          - ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)))
            • wassField s w Av (seq (N₀ + k * m)))
        = ∑ j ∈ Finset.range m,
            (((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
                • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
              - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
                • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
            + (seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
                - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
                  • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j))))) := by
    intro k
    have hsplit : ∑ j ∈ Finset.range m,
        (((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
          - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
        + (seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
            - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))))
        = (∑ j ∈ Finset.range m, (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m)))
          + (∑ j ∈ Finset.range m,
              (seq (N₀ + k * m + (j + 1)) - seq (N₀ + k * m + j))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show N₀ + k * m + (j + 1) = N₀ + k * m + j + 1 by ring]
      abel_nf
    rw [hsplit, Finset.sum_range_sub (fun j => seq (N₀ + k * m + j)) m]
    have hbijsum : ∑ j ∈ Finset.range m,
        wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
        = ∑ i ∈ s, wassPsi (m : ℝ) w Av i (seq (N₀ + k * m)) := by
      refine Finset.sum_nbij (fun j => idx (N₀ + k * m + j)) ?_ ?_ ?_ ?_
      · intro a ha
        have := (hbij k).mapsTo (by simpa using ha)
        simpa using this
      · exact (hbij k).injOn
      · exact (hbij k).surjOn
      · intro a _; rfl
    rw [← Finset.smul_sum, hbijsum, sum_wassPsi (m : ℝ) (hseqpos (N₀ + k * m)), smul_smul,
      mul_comm (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) (m : ℝ)]
    rw [Nat.add_zero]
    abel_nf
  -- the block estimate
  have hblockbd : ∀ k : ℕ,
      hsNorm (seq (N₀ + k * m + m) - (seq (N₀ + k * m)
          - ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)))
            • wassField s w Av (seq (N₀ + k * m))))
        ≤ ((m : ℝ) * ((m : ℝ) * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar))
              + (m : ℝ) * (K * (K * ((2 + K) ^ m
                  * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr)) + Cr))
          * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by
    intro k
    have hn₀ : N₀ ≤ N₀ + k * m := Nat.le_add_right _ _
    have hh0pos : (0 : ℝ) < 1 / (((N₀ + k * m : ℕ) : ℝ) + 1) := by positivity
    have hh01 : (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ ((N₀ + k * m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hDnn : (0 : ℝ) ≤ hsNorm (seq (N₀ + k * m) - Xstar) := hsNorm_nonneg _
    have hterm : ∀ j ∈ Finset.range m,
        hsNorm (((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
            - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
          + (seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
              - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
                • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))))
          ≤ ((m : ℝ) * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar))
              + (m : ℝ) * (K * (K * ((2 + K) ^ m
                  * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr)) + Cr)
            * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjm : j ≤ m := le_of_lt hj
      have hnj : N₀ ≤ N₀ + k * m + j := le_trans hn₀ (Nat.le_add_right _ _)
      have hidx := idx_mem_of_bijOn (s := s) hm hbij hnj
      have hhjpos : (0 : ℝ) < 1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1) := by positivity
      have hhjle : (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
          ≤ 1 / (((N₀ + k * m : ℕ) : ℝ) + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        push_cast
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith
      -- the difference of step sizes
      have hgap : (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
          ≤ (m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by
        have hjr : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
        have hcast : (((N₀ + k * m + j : ℕ) : ℝ) + 1)
            = ((N₀ + k * m : ℕ) : ℝ) + (j : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        exact one_div_sub_one_div_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hjr
      have hQnn : (0 : ℝ) ≤ K * ((2 + K) ^ m
          * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr := by
        have h1 : (0 : ℝ) ≤ (2 + K) ^ m := by positivity
        have h2 : (0 : ℝ) ≤ hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr := by linarith
        have := mul_nonneg hK0 (mul_nonneg h1 h2)
        linarith
      have hΨ0 := hΨHS (N₀ + k * m) (idx (N₀ + k * m + j)) hidx
      have hΨj := hΨHS (N₀ + k * m + j) (idx (N₀ + k * m + j)) hidx
      have hAHS : IsHilbertSchmidt ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
          - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j))) :=
        (hΨ0.real_smul _).sub (hΨj.real_smul _)
      have hρHS : IsHilbertSchmidt (seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
          - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))) := by
        have hid2 : seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
            - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
            = (seq (N₀ + k * m + j + 1) - seq (N₀ + k * m + j))
              + (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
                • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)) := by
          abel_nf
        rw [hid2]
        exact (hseqsub _ _).add (hΨj.real_smul _)
      refine (hsNorm_add_le hAHS hρHS).trans ?_
      -- the two summands
      have hAbd : hsNorm ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
          - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
          ≤ ((m : ℝ) * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar))
              + (m : ℝ) * (K * (K * ((2 + K) ^ m
                  * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr)))
            * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by
        have hidA : (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
            - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j))
            = ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1)))
                • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
              + (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
                • (wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
                  - wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j))) := by
          rw [sub_smul, smul_sub]
          abel_nf
        rw [hidA]
        refine (hsNorm_add_le (hΨ0.real_smul _) ((hΨ0.sub hΨj).real_smul _)).trans ?_
        rw [hsNorm_real_smul, hsNorm_real_smul,
          abs_of_nonneg (by linarith [hhjle] : (0:ℝ) ≤ (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
            - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))),
          abs_of_nonneg hhjpos.le]
        have hb1 : ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1)))
            * hsNorm (wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m)))
            ≤ ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2)
              * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar)) := by
          have hbd := hΨbd (N₀ + k * m) (idx (N₀ + k * m + j)) hidx
          rw [← hKdef] at hbd
          exact mul_le_mul hgap hbd (hsNorm_nonneg _) (by positivity)
        have hQj : hsNorm (wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
            - wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
            ≤ K * ((m : ℝ) * ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
              * (K * ((2 + K) ^ m
                  * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr))) := by
          have hlip := hΨlip (N₀ + k * m) (N₀ + k * m + j) (idx (N₀ + k * m + j)) hidx
          rw [← hKdef] at hlip
          refine hlip.trans ?_
          refine mul_le_mul_of_nonneg_left ?_ hK0
          have hqq := hQ (N₀ + k * m) hn₀ j hjm
          rw [show seq (N₀ + k * m) - seq (N₀ + k * m + j)
            = -(seq (N₀ + k * m + j) - seq (N₀ + k * m)) by abel_nf, hsNorm_neg']
          refine hqq.trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hjm
        have hb2 : (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
            * hsNorm (wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
              - wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
            ≤ (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
              * (K * ((m : ℝ) * ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
                * (K * ((2 + K) ^ m
                    * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr)))) :=
          mul_le_mul hhjle hQj (hsNorm_nonneg _) hh0pos.le
        have hfin : ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2)
              * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar))
            + (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
              * (K * ((m : ℝ) * ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
                * (K * ((2 + K) ^ m
                    * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr))))
            = ((m : ℝ) * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar))
              + (m : ℝ) * (K * (K * ((2 + K) ^ m
                  * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr)))
            * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by ring
        linarith [hb1, hb2, hfin]
      have hρbd : hsNorm (seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
            - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j))))
          ≤ Cr * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by
        refine (hstep (N₀ + k * m + j) hnj).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hCr
        exact pow_le_pow_left₀ hhjpos.le hhjle 2
      linarith [hAbd, hρbd]
    have hHSterm : ∀ j ∈ Finset.range m, IsHilbertSchmidt
        (((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m))
          - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
        + (seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
            - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j))))) := by
      intro j _
      have hnj : N₀ ≤ N₀ + k * m + j := le_trans hn₀ (Nat.le_add_right _ _)
      have hidx := idx_mem_of_bijOn (s := s) hm hbij hnj
      have hΨ0 := hΨHS (N₀ + k * m) (idx (N₀ + k * m + j)) hidx
      have hΨj := hΨHS (N₀ + k * m + j) (idx (N₀ + k * m + j)) hidx
      refine ((hΨ0.real_smul _).sub (hΨj.real_smul _)).add ?_
      have hid2 : seq (N₀ + k * m + j + 1) - (seq (N₀ + k * m + j)
          - (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
            • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)))
          = (seq (N₀ + k * m + j + 1) - seq (N₀ + k * m + j))
            + (1 / (((N₀ + k * m + j : ℕ) : ℝ) + 1))
              • wassPsi (m : ℝ) w Av (idx (N₀ + k * m + j)) (seq (N₀ + k * m + j)) := by
        abel_nf
      rw [hid2]
      exact (hseqsub _ _).add (hΨj.real_smul _)
    rw [hblockid k]
    refine (hsNorm_sum_le hHSterm).trans ?_
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  -- rewrite the block estimate with the block step size
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpowm : (0 : ℝ) ≤ (2 + K) ^ m := by positivity
  obtain ⟨Cb, hCbdef⟩ : ∃ c : ℝ, c = (K + K ^ 2 * (2 + K) ^ m)
      + (K * Sstar + K ^ 2 * (2 + K) ^ m * (Sstar + Cr) + K * Cr + Cr) := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by
    rw [hCbdef]
    have h1 : (0 : ℝ) ≤ K ^ 2 * (2 + K) ^ m := by positivity
    nlinarith [hK0, hS0, hCr, h1, hpowm]
  have hstepblock : ∀ k : ℕ,
      hsNorm (seq (N₀ + (k + 1) * m) - (seq (N₀ + k * m)
          - ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)))
            • wassField s w Av (seq (N₀ + k * m))))
        ≤ Cb * (1 + hsNorm (seq (N₀ + k * m) - Xstar))
          * ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) ^ 2 := by
    intro k
    rw [show N₀ + (k + 1) * m = N₀ + k * m + m by ring]
    refine (hblockbd k).trans ?_
    have hDnn : (0 : ℝ) ≤ hsNorm (seq (N₀ + k * m) - Xstar) := hsNorm_nonneg _
    have hh2 : (0 : ℝ) ≤ (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by positivity
    have hcoef : (m : ℝ) * ((m : ℝ) * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar))
          + (m : ℝ) * (K * (K * ((2 + K) ^ m
              * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr)) + Cr)
        ≤ Cb * (1 + hsNorm (seq (N₀ + k * m) - Xstar)) * (m : ℝ) ^ 2 := by
      have ha : (K + K ^ 2 * (2 + K) ^ m) ≤ Cb := by
        rw [hCbdef]
        nlinarith [hK0, hS0, hCr, hpowm, mul_nonneg (mul_nonneg hK0 hK0) hpowm]
      have hb : (K * Sstar + K ^ 2 * (2 + K) ^ m * (Sstar + Cr) + K * Cr + Cr) ≤ Cb := by
        rw [hCbdef]
        nlinarith [hK0, hpowm, mul_nonneg hK0 hK0]
      have hexp : (m : ℝ) * ((m : ℝ) * (K * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar))
            + (m : ℝ) * (K * (K * ((2 + K) ^ m
                * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr)) + Cr)
          ≤ (m : ℝ) ^ 2 * ((K + K ^ 2 * (2 + K) ^ m) * hsNorm (seq (N₀ + k * m) - Xstar)
            + (K * Sstar + K ^ 2 * (2 + K) ^ m * (Sstar + Cr) + K * Cr + Cr)) := by
        have hprod : (0 : ℝ) ≤ (m : ℝ) * Cr * ((m : ℝ) - 1) :=
          mul_nonneg (mul_nonneg (by linarith) hCr) (by linarith)
        nlinarith [hprod]
      refine hexp.trans ?_
      have hmain : (K + K ^ 2 * (2 + K) ^ m) * hsNorm (seq (N₀ + k * m) - Xstar)
          + (K * Sstar + K ^ 2 * (2 + K) ^ m * (Sstar + Cr) + K * Cr + Cr)
          ≤ Cb * (1 + hsNorm (seq (N₀ + k * m) - Xstar)) := by
        nlinarith [ha, hb, hDnn]
      have hm2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
      nlinarith [hmain, hm2]
    have hfac : ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) ^ 2
        = (m : ℝ) ^ 2 * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) ^ 2 := by ring
    rw [hfac]
    nlinarith [hcoef, hh2]
  -- step-size comparisons
  have hlamle : ∀ k : ℕ, (m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
      ≤ (m : ℝ) / ((k : ℝ) + 1) := by
    intro k
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hkm : (k : ℝ) ≤ (k : ℝ) * (m : ℝ) := by nlinarith [hm1, Nat.cast_nonneg (α := ℝ) k]
    have hN : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
    have hcast : ((N₀ + k * m : ℕ) : ℝ) = (N₀ : ℝ) + (k : ℝ) * (m : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [hkm, hN, hm1]
  have hlamge : ∀ k : ℕ, (m : ℝ) / (((N₀ : ℝ) + 1 + (m : ℝ)) * ((k : ℝ) + 1))
      ≤ (m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) := by
    intro k
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hN : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have hcast : ((N₀ + k * m : ℕ) : ℝ) = (N₀ : ℝ) + (k : ℝ) * (m : ℝ) := by push_cast; ring
    rw [hcast]
    have hXY : ((N₀ : ℝ) + (k : ℝ) * (m : ℝ)) + 1
        ≤ ((N₀ : ℝ) + 1 + (m : ℝ)) * ((k : ℝ) + 1) := by
      nlinarith [hN, hk, hm1]
    nlinarith [mul_le_mul_of_nonneg_left hXY (by linarith : (0 : ℝ) ≤ (m : ℝ))]
  have hlamtend : Tendsto (fun k : ℕ => (m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)))
      atTop (nhds 0) := by
    refine squeeze_zero (fun k => by positivity) hlamle ?_
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using h1.inv_tendsto_atTop.const_mul (m : ℝ)
  have hlamnn : ∀ k : ℕ, (0 : ℝ) ≤ (m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) := by
    intro k; positivity
  -- a starting block index where all step-size conditions hold
  obtain ⟨κ, hκdef⟩ : ∃ x : ℝ, x = α * α / (2 * (β * (β * β))) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have hcond : ∀ᶠ k : ℕ in atTop,
      κ * ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) ≤ 1
        ∧ ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) * (wassLipConst α β) ^ 2 ≤ κ / 2
        ∧ Cb * ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) ≤ κ / 8 := by
    have e1 : Tendsto (fun k : ℕ => κ * ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))))
        atTop (nhds 0) := by simpa using hlamtend.const_mul κ
    have e2 : Tendsto (fun k : ℕ =>
        ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) * (wassLipConst α β) ^ 2)
        atTop (nhds 0) := by simpa using hlamtend.mul_const ((wassLipConst α β) ^ 2)
    have e3 : Tendsto (fun k : ℕ => Cb * ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))))
        atTop (nhds 0) := by simpa using hlamtend.const_mul Cb
    filter_upwards [e1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      e2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < κ / 2)),
      e3.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < κ / 8))] with k h1 h2 h3
    exact ⟨h1.le, h2.le, h3.le⟩
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hcond
  -- convergence of the block sequence
  have hxconv : Tendsto (fun k : ℕ => hsNorm (seq (N₀ + (K₀ + k) * m) - Xstar))
      atTop (nhds 0) := by
    refine tendsto_hsNorm_sub_isWassersteinPoint' (Cr := Cb)
      (lam := fun k : ℕ => (m : ℝ) * (1 / (((N₀ + (K₀ + k) * m : ℕ) : ℝ) + 1)))
      hα hβ hw hwsum hA hAα hAβ hXstarW hXstarα hXstarβ
      (fun k => hseqpos _) (fun k => hseqa _) (fun k => hseqb _) (fun k => hseqHS _)
      hCb0 (fun k => hlamnn _) ?_ ?_ ?_ ?_ ?_ ?_
    · intro k
      have := (hK₀ (K₀ + k) (Nat.le_add_right _ _)).1
      rwa [← hκdef]
    · intro k
      have := (hK₀ (K₀ + k) (Nat.le_add_right _ _)).2.1
      rwa [← hκdef]
    · intro k
      have := (hK₀ (K₀ + k) (Nat.le_add_right _ _)).2.2
      rwa [← hκdef]
    · intro k
      exact hstepblock (K₀ + k)
    · -- divergence of the step sizes
      have hc : (0 : ℝ) < (m : ℝ) / (((N₀ : ℝ) + 1 + (m : ℝ)) * ((K₀ : ℝ) + 1)) := by
        positivity
      have hcomp : ∀ n : ℕ,
          (m : ℝ) / (((N₀ : ℝ) + 1 + (m : ℝ)) * ((K₀ : ℝ) + 1))
              * ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)
            ≤ ∑ k ∈ Finset.range n,
              (m : ℝ) * (1 / (((N₀ + (K₀ + k) * m : ℕ) : ℝ) + 1)) := by
        intro n
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        refine le_trans ?_ (hlamge (K₀ + k))
        have hcast : ((K₀ + k : ℕ) : ℝ) = (K₀ : ℝ) + (k : ℝ) := by push_cast; ring
        rw [hcast, div_mul_eq_mul_div, mul_one_div, div_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have hK : (0 : ℝ) ≤ (K₀ : ℝ) := Nat.cast_nonneg _
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        have hN : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
        have hbase : (0 : ℝ) ≤ (N₀ : ℝ) + 1 + (m : ℝ) := by linarith
        nlinarith [hK, hk, hN, hm1, hbase, mul_nonneg hK hk,
          mul_nonneg (mul_nonneg hbase hK) hk, mul_nonneg hbase hK,
          mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ)) hbase) (mul_nonneg hK hk)]
      refine tendsto_atTop_mono hcomp ?_
      exact Filter.Tendsto.const_mul_atTop hc Real.tendsto_sum_range_one_div_nat_succ_atTop
    · -- square-summability
      have hsq : Summable (fun k : ℕ => ((m : ℝ) / ((k : ℝ) + 1)) ^ 2) := by
        have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
          Real.summable_one_div_nat_pow.mpr one_lt_two
        have h1 : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) :=
          (summable_nat_add_iff 1).2 h0
        have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
          refine h1.congr fun n => ?_
          push_cast
          ring
        have := h2.mul_left ((m : ℝ) ^ 2)
        refine this.congr fun n => ?_
        rw [div_pow]
        ring
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsq
      have hle := hlamle (K₀ + k)
      have hmono : (m : ℝ) / (((K₀ + k : ℕ) : ℝ) + 1) ≤ (m : ℝ) / ((k : ℝ) + 1) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        push_cast
        have : (0 : ℝ) ≤ (K₀ : ℝ) := Nat.cast_nonneg _
        linarith
      have hfin : (m : ℝ) * (1 / (((N₀ + (K₀ + k) * m : ℕ) : ℝ) + 1))
          ≤ (m : ℝ) / ((k : ℝ) + 1) := le_trans hle hmono
      exact pow_le_pow_left₀ (hlamnn _) hfin 2
  -- transfer to the whole sequence
  intro ε hε
  obtain ⟨Qmax, hQmaxdef⟩ : ∃ x : ℝ, x = K * ((2 + K) ^ m * (1 + Sstar + Cr)) + Cr := ⟨_, rfl⟩
  have hQmax0 : 0 ≤ Qmax := by
    rw [hQmaxdef]
    have h1 : (0 : ℝ) ≤ (2 + K) ^ m * (1 + Sstar + Cr) := by positivity
    nlinarith [hK0, hCr, h1]
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (hxconv.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < min (ε / 2) 1)))
  have hlamQ : Tendsto (fun k : ℕ => ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) * Qmax)
      atTop (nhds 0) := by simpa using hlamtend.mul_const Qmax
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1
    (hlamQ.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2)))
  obtain ⟨M, hMdef⟩ : ∃ x : ℕ, x = max (K₀ + J) K₂ + 1 := ⟨_, rfl⟩
  refine ⟨N₀ + M * m, ?_⟩
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = N₀ + d := ⟨n - N₀, by omega⟩
  have hdM : M * m ≤ d := by omega
  obtain ⟨k, j, hkj, hjm, hkM⟩ : ∃ k j : ℕ, d = k * m + j ∧ j < m ∧ M ≤ k := by
    refine ⟨d / m, d % m, ?_, Nat.mod_lt _ hm, ?_⟩
    · rw [Nat.mul_comm]
      exact (Nat.div_add_mod d m).symm
    · rw [Nat.le_div_iff_mul_le hm]
      exact hdM
  have hMle : max (K₀ + J) K₂ ≤ M := by rw [hMdef]; omega
  have hkK : K₀ + J ≤ k := le_trans (le_trans (le_max_left _ _) hMle) hkM
  have hkK₂ : K₂ ≤ k := le_trans (le_trans (le_max_right _ _) hMle) hkM
  have hn₀ : N₀ ≤ N₀ + k * m := Nat.le_add_right _ _
  -- the block point is close to the barycentre
  have hDk : hsNorm (seq (N₀ + k * m) - Xstar) < min (ε / 2) 1 := by
    have hkk : K₀ + (k - K₀) = k := by omega
    have := hJ (k - K₀) (by omega)
    rwa [hkk] at this
  -- the within-block drift is small
  have hdriftk : hsNorm (seq (N₀ + k * m + j) - seq (N₀ + k * m)) < ε / 2 := by
    have hq := hQ (N₀ + k * m) hn₀ j (le_of_lt hjm)
    have hjr : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hjm
    have hDle : hsNorm (seq (N₀ + k * m) - Xstar) ≤ 1 := le_of_lt (lt_of_lt_of_le hDk (min_le_right _ _))
    have hQle : K * ((2 + K) ^ m * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr
        ≤ Qmax := by
      rw [hQmaxdef]
      have h1 : (0 : ℝ) ≤ (2 + K) ^ m := by positivity
      have h2 : (0 : ℝ) ≤ K * (2 + K) ^ m := mul_nonneg hK0 h1
      nlinarith [h2, hDle]
    have hbound : hsNorm (seq (N₀ + k * m + j) - seq (N₀ + k * m))
        ≤ ((m : ℝ) * (1 / (((N₀ + k * m : ℕ) : ℝ) + 1))) * Qmax := by
      refine hq.trans ?_
      have hh0nn : (0 : ℝ) ≤ 1 / (((N₀ + k * m : ℕ) : ℝ) + 1) := by positivity
      have hQnn : (0 : ℝ) ≤ K * ((2 + K) ^ m
          * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr := by
        have h1 : (0 : ℝ) ≤ (2 + K) ^ m := by positivity
        have h2 : (0 : ℝ) ≤ hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr := by
          have := hsNorm_nonneg (seq (N₀ + k * m) - Xstar); linarith
        nlinarith [hK0, hCr, mul_nonneg h1 h2]
      have hstep1 : (j : ℝ) * ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1))
            * (K * ((2 + K) ^ m
              * (hsNorm (seq (N₀ + k * m) - Xstar) + Sstar + Cr)) + Cr))
          ≤ (m : ℝ) * ((1 / (((N₀ + k * m : ℕ) : ℝ) + 1)) * Qmax) := by
        refine mul_le_mul hjr ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hQle hh0nn
      refine hstep1.trans (le_of_eq ?_)
      ring
    exact lt_of_le_of_lt hbound (hK₂ k hkK₂)
  -- combine
  have htri : hsNorm (seq (N₀ + (k * m + j)) - Xstar)
      ≤ hsNorm (seq (N₀ + k * m + j) - seq (N₀ + k * m))
        + hsNorm (seq (N₀ + k * m) - Xstar) := by
    have hid : seq (N₀ + (k * m + j)) - Xstar
        = (seq (N₀ + k * m + j) - seq (N₀ + k * m)) + (seq (N₀ + k * m) - Xstar) := by
      rw [show N₀ + (k * m + j) = N₀ + k * m + j by ring]
      abel_nf
    rw [hid]
    exact hsNorm_add_le (hseqsub _ _) (hseqHS _)
  rw [hkj]
  have hDk2 : hsNorm (seq (N₀ + k * m) - Xstar) < ε / 2 :=
    lt_of_lt_of_le hDk (min_le_left _ _)
  linarith [htri, hdriftk, hDk2]

/-! ### The cyclic index scheme -/

/-- **The cyclic scheme `i_n ≡ n + 1 (mod m)` visits every index exactly once per block.**  This
is the hypothesis `hbij` of the no-dice theorem for the paper's concrete iteration. -/
lemma bijOn_cyclic {m : ℕ} (hm : 0 < m) (c : ℕ) :
    Set.BijOn (fun j : ℕ => (⟨(c + j) % m, Nat.mod_lt _ hm⟩ : Fin m))
      (↑(Finset.range m)) (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => (⟨(c + j) % m, Nat.mod_lt _ hm⟩ : Fin m))
      (↑(Finset.range m)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h : (c + a) % m = (c + b) % m := by
      simpa [Fin.ext_iff] using hab
    have hmod : a % m = b % m := Nat.ModEq.add_left_cancel' c h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  refine ⟨fun a _ => by simp, hinj, ?_⟩
  have hinj' : Set.InjOn (fun j : ℕ => (⟨(c + j) % m, Nat.mod_lt _ hm⟩ : Fin m))
      (Finset.range m : Finset ℕ) := hinj
  have himg : Finset.image (fun j : ℕ => (⟨(c + j) % m, Nat.mod_lt _ hm⟩ : Fin m))
      (Finset.range m) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injOn hinj', Finset.card_range, Fintype.card_fin]
  intro i _
  have : i ∈ Finset.image (fun j : ℕ => (⟨(c + j) % m, Nat.mod_lt _ hm⟩ : Fin m))
      (Finset.range m) := by rw [himg]; exact Finset.mem_univ i
  rw [Finset.mem_image] at this
  obtain ⟨j, hj, hji⟩ := this
  exact ⟨j, by simpa using hj, hji⟩

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
