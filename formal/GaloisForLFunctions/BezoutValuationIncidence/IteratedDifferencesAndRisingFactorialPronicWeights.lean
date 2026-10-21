import GaloisForLFunctions.BezoutValuationIncidence.SharpCutoffTypeIStopsAtFourThirds

/-!
# Iterated differences and the rising-factorial pronic weights

Tools for cross-scale laws of every order.

**Higher pronic weights.** With the rising product `R(x, m) = x(x+1)⋯(x+m-1)`, the weights
`u_k(M) = (k+1)!/R(M, k+2)` start at the pronic weight `u_0(M) = 1/(M(M+1))`. Each is the backward
difference of the previous one, `u_k(M) - u_k(M+1) = u_{k+1}(M)`, by the same telescoping as the complex
reciprocal rising factorials of the factorial series. They are positive, antitone, and satisfy
`u_k(M) ≤ (k+1)!/M^{k+2}`.

**Iterated backward differences** `Δf(n) = f(n) - f(n+1)`.
* *Leibniz bound:* if `|Δʳ g| ≤ μ_r` with every `μ_r` antitone, then
  `|Δˢ(fg)(n)| ≤ 2ˢ Σ_{t ≤ s} |Δᵗ f(n)| μ_{s-t}(n)`.
* *Step `j`:* the weight `m ↦ u_i(j(m+1) + t)` has `|Δʳ| ≤ jʳ u_{i+r}(j(m+1) + t)`. One difference
  of step `j` is a sum of `j` differences of step one.

**Periodic kernels.** A `p`-periodic sequence `X` with zero period sum has the periodic centred primitive
`Y(n) = Σ_{k<n} X(k) - mean`, with zero period sum and `|Y| ≤ 2p max|X|`. Iterating one summation by
parts and one centring gives, for weights vanishing outside `[s+1, b)`,

`|Σ_{n<b} x(n) D(n)| ≤ (2p)^{s+1} B Σ_{n<b} |Δ^{s+1} x(n)|`  (`|D| ≤ B`).
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The rising-factorial pronic weights -/

/-- The rising product `R(x, m) = x(x+1)⋯(x+m-1)`. -/
def risingProdReal (x : ℝ) (m : ℕ) : ℝ := ∏ t ∈ range m, (x + t)

theorem risingProdReal_succ (x : ℝ) (m : ℕ) :
    risingProdReal x (m + 1) = risingProdReal x m * (x + m) := by
  rw [risingProdReal, risingProdReal, prod_range_succ]

theorem risingProdReal_succ' (x : ℝ) (m : ℕ) :
    risingProdReal x (m + 1) = x * risingProdReal (x + 1) m := by
  rw [risingProdReal, risingProdReal, prod_range_succ']
  rw [prod_congr rfl fun t _ => show x + ((t + 1 : ℕ) : ℝ) = (x + 1) + t by push_cast; ring]
  simp [mul_comm]

theorem risingProdReal_pos {x : ℝ} (hx : 0 < x) (m : ℕ) : 0 < risingProdReal x m :=
  prod_pos fun t _ => by positivity

theorem pow_le_risingProdReal {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x ^ m ≤ risingProdReal x m := by
  induction m with
  | zero => simp [risingProdReal]
  | succ m ih =>
    rw [risingProdReal_succ, pow_succ]
    exact mul_le_mul ih (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) hx
      ((pow_nonneg hx m).trans ih)

/-- The higher pronic weight `u_k(M) = (k+1)!/(M(M+1)⋯(M+k+1))`. -/
def pronicWeight (k M : ℕ) : ℝ := ((k + 1).factorial : ℝ) / risingProdReal M (k + 2)

theorem pronicWeight_zero (M : ℕ) : pronicWeight 0 M = pw M := by
  simp [pronicWeight, risingProdReal, prod_range_succ, pw]

theorem pronicWeight_pos {k M : ℕ} (hM : 1 ≤ M) : 0 < pronicWeight k M := by
  have : (0 : ℝ) < M := by exact_mod_cast hM
  exact div_pos (by positivity) (risingProdReal_pos this _)

/-- **The difference law.** `u_k(M) - u_k(M+1) = u_{k+1}(M)` for `1 ≤ M`. -/
theorem pronicWeight_sub_succ {k M : ℕ} (hM : 1 ≤ M) :
    pronicWeight k M - pronicWeight k (M + 1) = pronicWeight (k + 1) M := by
  have hx : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 := risingProdReal_succ (M : ℝ) (k + 2)
  have h2 := risingProdReal_succ' (M : ℝ) (k + 2)
  have hP := risingProdReal_pos hx (k + 2)
  have hQ := risingProdReal_pos (by linarith : (0 : ℝ) < (M : ℝ) + 1) (k + 2)
  have hR := risingProdReal_pos hx (k + 2 + 1)
  unfold pronicWeight
  rw [show ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 by push_cast; ring, show k + 1 + 2 = k + 2 + 1 by ring]
  rw [show ((k + 1).factorial : ℝ) / risingProdReal M (k + 2) =
      ((k + 1).factorial : ℝ) * ((M : ℝ) + ((k + 2 : ℕ) : ℝ)) / risingProdReal M (k + 2 + 1) by
    rw [h1]; field_simp]
  rw [show ((k + 1).factorial : ℝ) / risingProdReal ((M : ℝ) + 1) (k + 2) =
      ((k + 1).factorial : ℝ) * (M : ℝ) / risingProdReal M (k + 2 + 1) by
    rw [h2]; field_simp]
  rw [← sub_div, Nat.factorial_succ (k + 1)]
  congr 1
  push_cast
  ring

theorem pronicWeight_succ_le {k M : ℕ} (hM : 1 ≤ M) : pronicWeight k (M + 1) ≤ pronicWeight k M := by
  have := pronicWeight_sub_succ (k := k) hM
  have := pronicWeight_pos (k := k + 1) hM
  linarith

theorem pronicWeight_anti {k M M' : ℕ} (hM : 1 ≤ M) (h : M ≤ M') :
    pronicWeight k M' ≤ pronicWeight k M := by
  induction M' with
  | zero => omega
  | succ M' ih =>
    rcases Nat.lt_or_ge M' M with h' | h'
    · rw [show M' + 1 = M by omega]
    · exact (pronicWeight_succ_le (by omega)).trans (ih h')

theorem pronicWeight_le {k M : ℕ} (hM : 1 ≤ M) :
    pronicWeight k M ≤ ((k + 1).factorial : ℝ) / (M : ℝ) ^ (k + 2) := by
  have hx : (0 : ℝ) < M := by exact_mod_cast hM
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_risingProdReal hx.le _)

/-- `u_k(A + m) ≤ (k+1)!/(m+1)²` for `1 ≤ A`. -/
theorem pronicWeight_add_le {k A : ℕ} (hA : 1 ≤ A) (m : ℕ) :
    pronicWeight k (A + m) ≤ ((k + 1).factorial : ℝ) * (1 / ((m : ℝ) + 1) ^ 2) := by
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hAm : (m : ℝ) + 1 ≤ ((A + m : ℕ) : ℝ) := by push_cast; linarith
  refine (pronicWeight_le (by omega)).trans ?_
  rw [mul_one_div]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  calc ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ (k + 2) := pow_le_pow_right₀ hm (by omega)
    _ ≤ ((A + m : ℕ) : ℝ) ^ (k + 2) := pow_le_pow_left₀ (by positivity) hAm _

theorem summable_pronicWeight_add {k A : ℕ} (hA : 1 ≤ A) :
    Summable fun m : ℕ => pronicWeight k (A + m) := by
  have hs : Summable fun m : ℕ => ((k + 1).factorial : ℝ) * (1 / ((m + 1 : ℕ) : ℝ) ^ 2) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
  refine Summable.of_nonneg_of_le (fun m => (pronicWeight_pos (by omega)).le) (fun m => ?_) hs
  have := pronicWeight_add_le (k := k) hA m
  push_cast
  exact this

/-! ## §2. Iterated backward differences -/

/-- The backward difference `Δf(n) = f(n) - f(n+1)`. -/
def bdiff (f : ℕ → ℝ) : ℕ → ℝ := fun n => f n - f (n + 1)

theorem bdiff_iter_add (r : ℕ) : ∀ f g : ℕ → ℝ,
    bdiff^[r] (fun n => f n + g n) = fun n => bdiff^[r] f n + bdiff^[r] g n := by
  induction r with
  | zero => intro f g; rfl
  | succ r ih =>
    intro f g
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [show bdiff (fun n => f n + g n) = fun n => bdiff f n + bdiff g n by
      funext n; simp only [bdiff]; ring, ih]

theorem bdiff_iter_sum (r : ℕ) {ι : Type*} (s : Finset ι) : ∀ F : ι → ℕ → ℝ,
    bdiff^[r] (fun n => ∑ i ∈ s, F i n) = fun n => ∑ i ∈ s, bdiff^[r] (F i) n := by
  induction r with
  | zero => intro F; rfl
  | succ r ih =>
    intro F
    rw [Function.iterate_succ_apply]
    rw [show bdiff (fun n => ∑ i ∈ s, F i n) = fun n => ∑ i ∈ s, bdiff (F i) n by
      funext n; simp only [bdiff, sum_sub_distrib], ih]
    funext n
    exact sum_congr rfl fun i _ => by rw [Function.iterate_succ_apply]

theorem bdiff_iter_shift (r t : ℕ) : ∀ f : ℕ → ℝ,
    bdiff^[r] (fun n => f (n + t)) = fun n => bdiff^[r] f (n + t) := by
  induction r with
  | zero => intro f; rfl
  | succ r ih =>
    intro f
    rw [Function.iterate_succ_apply]
    rw [show bdiff (fun n => f (n + t)) = fun n => bdiff f (n + t) by
      funext n; simp only [bdiff]; rw [show n + 1 + t = n + t + 1 by ring], ih]
    funext n
    rw [Function.iterate_succ_apply]

theorem bdiff_iter_apply_zero_of_vanish (S : ℕ) : ∀ f : ℕ → ℝ, (∀ n ≤ S, f n = 0) →
    bdiff^[S] f 0 = 0 := by
  induction S with
  | zero => intro f hf; exact hf 0 le_rfl
  | succ S ih =>
    intro f hf
    rw [Function.iterate_succ_apply]
    exact ih _ fun n hn => by simp only [bdiff, hf n (by omega), hf (n + 1) (by omega), sub_zero]

/-- **The Leibniz bound.** If `|Δʳ g(m)| ≤ μ_r(m)` with antitone `μ_r`, then
`|Δˢ(fg)(n)| ≤ 2ˢ Σ_{t ≤ s} |Δᵗ f(n)| μ_{s-t}(n)`. -/
theorem abs_bdiff_iter_mul_le (s : ℕ) : ∀ (f g : ℕ → ℝ) (μ : ℕ → ℕ → ℝ),
    (∀ r m, |bdiff^[r] g m| ≤ μ r m) → (∀ r, Antitone (μ r)) → ∀ n,
      |bdiff^[s] (fun m => f m * g m) n| ≤
        2 ^ s * ∑ t ∈ range (s + 1), |bdiff^[t] f n| * μ (s - t) n := by
  induction s with
  | zero =>
    intro f g μ hg _ n
    simp only [Function.iterate_zero, id, pow_zero, zero_add, range_one, sum_singleton, one_mul,
      Nat.sub_zero]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hg 0 n) (abs_nonneg _)
  | succ s ih =>
    intro f g μ hg hμ n
    have hμ0 : ∀ r m, 0 ≤ μ r m := fun r m => (abs_nonneg _).trans (hg r m)
    have hsplit : bdiff (fun m => f m * g m) =
        fun m => bdiff f m * g (m + 1) + f m * bdiff g m := by
      funext m; simp only [bdiff]; ring
    rw [Function.iterate_succ_apply, hsplit, bdiff_iter_add]
    -- the two halves
    have h1 := ih (bdiff f) (fun m => g (m + 1)) μ (fun r m => by
      rw [bdiff_iter_shift r 1 g]
      exact (hg r (m + 1)).trans (hμ r (Nat.le_succ m))) hμ n
    have h2 := ih f (bdiff g) (fun r m => μ (r + 1) m) (fun r m => by
      rw [← Function.iterate_succ_apply]; exact hg (r + 1) m) (fun r => hμ (r + 1)) n
    set a : ℕ → ℝ := fun t => |bdiff^[t] f n| * μ (s + 1 - t) n
    have ha : ∀ t, 0 ≤ a t := fun t => mul_nonneg (abs_nonneg _) (hμ0 _ _)
    have e1 : ∑ t ∈ range (s + 1), |bdiff^[t] (bdiff f) n| * μ (s - t) n =
        ∑ t ∈ range (s + 1), a (t + 1) := sum_congr rfl fun t ht => by
      simp only [a]
      rw [← Function.iterate_succ_apply, show s + 1 - (t + 1) = s - t by omega]
    have e2 : ∑ t ∈ range (s + 1), |bdiff^[t] f n| * μ (s - t + 1) n =
        ∑ t ∈ range (s + 1), a t := sum_congr rfl fun t ht => by
      simp only [a]
      rw [show s - t + 1 = s + 1 - t by have := mem_range.mp ht; omega]
    rw [e1] at h1
    rw [e2] at h2
    have hA : ∑ t ∈ range (s + 1), a (t + 1) ≤ ∑ t ∈ range (s + 1 + 1), a t := by
      rw [Finset.sum_range_succ' a (s + 1)]; linarith [ha 0]
    have hB : ∑ t ∈ range (s + 1), a t ≤ ∑ t ∈ range (s + 1 + 1), a t := by
      rw [Finset.sum_range_succ a (s + 1)]; linarith [ha (s + 1)]
    calc |bdiff^[s] (fun m => bdiff f m * g (m + 1)) n + bdiff^[s] (fun m => f m * bdiff g m) n|
        ≤ |bdiff^[s] (fun m => bdiff f m * g (m + 1)) n| +
            |bdiff^[s] (fun m => f m * bdiff g m) n| := abs_add_le _ _
      _ ≤ 2 ^ s * ∑ t ∈ range (s + 1), a (t + 1) + 2 ^ s * ∑ t ∈ range (s + 1), a t :=
          add_le_add h1 h2
      _ ≤ 2 ^ (s + 1) * ∑ t ∈ range (s + 1 + 1), a t := by
          rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) s]

/-! ## §3. Differences of step `j` -/

/-- **Step-`j` differences.** For `1 ≤ j`, the weight `m ↦ u_i(j(m+1) + t)` satisfies
`|Δʳ| ≤ jʳ u_{i+r}(j(m+1) + t)`. -/
theorem abs_bdiff_iter_pronicWeight_le {j : ℕ} (hj : 1 ≤ j) (r : ℕ) : ∀ i t m : ℕ,
    |bdiff^[r] (fun m => pronicWeight i (j * (m + 1) + t)) m| ≤
      (j : ℝ) ^ r * pronicWeight (i + r) (j * (m + 1) + t) := by
  induction r with
  | zero =>
    intro i t m
    simp only [Function.iterate_zero, id, pow_zero, one_mul, add_zero]
    exact (abs_of_pos (pronicWeight_pos (by nlinarith))).le
  | succ r ih =>
    intro i t m
    have hstep : bdiff (fun m => pronicWeight i (j * (m + 1) + t)) =
        fun m => ∑ s ∈ range j, pronicWeight (i + 1) (j * (m + 1) + (t + s)) := by
      funext m
      simp only [bdiff]
      have htel : ∀ L, ∑ s ∈ range L, pronicWeight (i + 1) (j * (m + 1) + (t + s)) =
          pronicWeight i (j * (m + 1) + t) - pronicWeight i (j * (m + 1) + t + L) := by
        intro L
        induction L with
        | zero => simp
        | succ L ihL =>
          rw [Finset.sum_range_succ, ihL, ← pronicWeight_sub_succ (by nlinarith),
            show j * (m + 1) + (t + L) = j * (m + 1) + t + L by ring,
            show j * (m + 1) + t + (L + 1) = j * (m + 1) + t + L + 1 by ring]
          ring
      rw [htel, show j * (m + 1 + 1) + t = j * (m + 1) + t + j by ring]
    rw [Function.iterate_succ_apply, hstep, bdiff_iter_sum]
    calc |∑ s ∈ range j, bdiff^[r] (fun m => pronicWeight (i + 1) (j * (m + 1) + (t + s))) m|
        ≤ ∑ s ∈ range j, |bdiff^[r] (fun m => pronicWeight (i + 1) (j * (m + 1) + (t + s))) m| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ range j, (j : ℝ) ^ r * pronicWeight (i + (r + 1)) (j * (m + 1) + t) := by
          refine sum_le_sum fun s _ => (ih (i + 1) (t + s) m).trans ?_
          rw [show i + 1 + r = i + (r + 1) by ring]
          exact mul_le_mul_of_nonneg_left (pronicWeight_anti (by nlinarith) (by omega))
            (by positivity)
      _ = (j : ℝ) ^ (r + 1) * pronicWeight (i + (r + 1)) (j * (m + 1) + t) := by
          rw [sum_const, card_range, nsmul_eq_mul, pow_succ]; ring

/-! ## §4. Periodic kernels: the centred primitive and iterated summation by parts -/

/-- The centred primitive `Y(n) = Σ_{k<n} X(k) - (1/p) Σ_{r<p} Σ_{k<r} X(k)`. -/
def centredPrimitive (p : ℕ) (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, X k - (∑ r ∈ range p, ∑ k ∈ range r, X k) / p

theorem centredPrimitive_succ_sub (p : ℕ) (X : ℕ → ℝ) (n : ℕ) :
    centredPrimitive p X (n + 1) - centredPrimitive p X n = X n := by
  simp only [centredPrimitive, Finset.sum_range_succ]; ring

theorem centredPrimitive_periodic {p : ℕ} {X : ℕ → ℝ} (hper : ∀ n, X (n + p) = X n)
    (h0 : ∑ n ∈ range p, X n = 0) (n : ℕ) :
    centredPrimitive p X (n + p) = centredPrimitive p X n := by
  simp only [centredPrimitive]
  rw [← sum_range_add_sum_Ico _ (by omega : n ≤ n + p), sum_Ico_eq_sum_range_of_periodic hper n, h0,
    add_zero]

theorem sum_range_centredPrimitive {p : ℕ} (hp : 0 < p) (X : ℕ → ℝ) :
    ∑ n ∈ range p, centredPrimitive p X n = 0 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [centredPrimitive]
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

theorem abs_centredPrimitive_le {p : ℕ} (hp : 0 < p) {X : ℕ → ℝ} (hper : ∀ n, X (n + p) = X n)
    (h0 : ∑ n ∈ range p, X n = 0) {B : ℝ} (hB : ∀ n, |X n| ≤ B) (n : ℕ) :
    |centredPrimitive p X n| ≤ 2 * p * B := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hG : ∀ m, |∑ k ∈ range m, X k| ≤ p * B := fun m => by
    have h := abs_sum_Ico_le_of_periodic hp hper h0 hB 0 m
    rwa [zero_add, ← range_eq_Ico] at h
  have hμ : |(∑ r ∈ range p, ∑ k ∈ range r, X k) / p| ≤ p * B := by
    rw [abs_div, abs_of_pos hpR, div_le_iff₀ hpR]
    calc |∑ r ∈ range p, ∑ k ∈ range r, X k| ≤ ∑ r ∈ range p, |∑ k ∈ range r, X k| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ range p, (p : ℝ) * B := sum_le_sum fun r _ => hG r
      _ = p * B * p := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  calc |centredPrimitive p X n| ≤ |∑ k ∈ range n, X k| + |(∑ r ∈ range p, ∑ k ∈ range r, X k) / p| :=
        abs_sub _ _
    _ ≤ p * B + p * B := add_le_add (hG n) hμ
    _ = 2 * p * B := by ring

/-- **Iterated summation by parts against a periodic kernel.** Let `D` be `p`-periodic with zero
period sum and `|D| ≤ B`, and let `x` vanish below `s + 1` and from `b` on. Then
`|Σ_{n<b} x(n) D(n)| ≤ (2p)^{s+1} B Σ_{n<b} |Δ^{s+1} x(n)|`. -/
theorem abs_sum_mul_periodic_le_iter {p : ℕ} (hp : 0 < p) (s : ℕ) : ∀ (D : ℕ → ℝ) (B : ℝ),
    (∀ n, D (n + p) = D n) → ∑ n ∈ range p, D n = 0 → (∀ n, |D n| ≤ B) →
    ∀ (x : ℕ → ℝ) (b : ℕ), (∀ n, n < s + 1 → x n = 0) → (∀ n, b ≤ n → x n = 0) →
      |∑ n ∈ range b, x n * D n| ≤
        (2 * p) ^ (s + 1) * B * ∑ n ∈ range b, |bdiff^[s + 1] x n| := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  -- one summation by parts against the primitive
  have hstep : ∀ (D : ℕ → ℝ) (x : ℕ → ℝ) (b : ℕ), x 0 = 0 → x b = 0 →
      ∑ n ∈ range b, x n * D n =
        ∑ n ∈ range b, bdiff x n * centredPrimitive p D (n + 1) := by
    intro D x b h0 hb
    rw [show ∑ n ∈ range b, x n * D n =
        ∑ n ∈ range b, x n * (centredPrimitive p D (n + 1) - centredPrimitive p D n) from
      sum_congr rfl fun n _ => by rw [centredPrimitive_succ_sub],
      sum_range_mul_sub_eq x (centredPrimitive p D) b h0 hb]
    rfl
  induction s with
  | zero =>
    intro D B hper h0 hB x b hx hxb
    rw [hstep D x b (hx 0 (by omega)) (hxb b le_rfl), mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul, mul_comm (|bdiff x n|)]
    have hY := abs_centredPrimitive_le hp hper h0 hB (n + 1)
    simp only [Function.iterate_one, zero_add, pow_one]
    nlinarith [abs_nonneg (bdiff x n)]
  | succ s ih =>
    intro D B hper h0 hB x b hx hxb
    rw [hstep D x b (hx 0 (by omega)) (hxb b le_rfl)]
    -- the shifted primitive is again a periodic kernel with zero period sum
    set D₂ : ℕ → ℝ := fun n => centredPrimitive p D (n + 1)
    have hper₂ : ∀ n, D₂ (n + p) = D₂ n := fun n => by
      simp only [D₂]; rw [show n + p + 1 = n + 1 + p by ring, centredPrimitive_periodic hper h0]
    have h0₂ : ∑ n ∈ range p, D₂ n = 0 := by
      have e : ∑ n ∈ range p, D₂ n = ∑ n ∈ Ico 1 (1 + p), centredPrimitive p D n := by
        rw [sum_Ico_eq_sum_range, show 1 + p - 1 = p by omega]
        exact sum_congr rfl fun n _ => by simp only [D₂]; rw [add_comm]
      rw [e, sum_Ico_eq_sum_range_of_periodic (centredPrimitive_periodic hper h0) 1,
        sum_range_centredPrimitive hp]
    have hB₂ : ∀ n, |D₂ n| ≤ 2 * p * B := fun n => abs_centredPrimitive_le hp hper h0 hB (n + 1)
    have h := ih D₂ (2 * p * B) hper₂ h0₂ hB₂ (bdiff x) b
      (fun n hn => by simp only [bdiff, hx n (by omega), hx (n + 1) (by omega), sub_zero])
      (fun n hn => by simp only [bdiff, hxb n hn, hxb (n + 1) (by omega), sub_zero])
    rw [show ∑ n ∈ range b, |bdiff^[s + 1] (bdiff x) n| = ∑ n ∈ range b, |bdiff^[s + 1 + 1] x n| from
      sum_congr rfl fun n _ => by rw [← Function.iterate_succ_apply]] at h
    calc |∑ n ∈ range b, bdiff x n * D₂ n|
        ≤ (2 * p) ^ (s + 1) * (2 * p * B) * ∑ n ∈ range b, |bdiff^[s + 1 + 1] x n| := h
      _ = (2 * p) ^ (s + 1 + 1) * B * ∑ n ∈ range b, |bdiff^[s + 1 + 1] x n| := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
