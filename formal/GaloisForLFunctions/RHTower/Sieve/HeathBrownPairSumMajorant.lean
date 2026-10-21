import GaloisForLFunctions.HTGeometry.LargeValuesDuality
import GaloisForLFunctions.RHTower.Sieve.DirichletPoly
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum

/-!
# Heath-Brown's pair sums: the ratio-kernel identity and the majorant principle

Heath-Brown's large values theorem (Guth–Maynard, Theorem 1.6) bounds the pair sum

`Σ_{t₁,t₂∈W} |Σ_{n∈S} a_n n^{i(t₁ − t₂)}|²`,   `n^{it} = e^{it log n}`,

over a finite set `W ⊂ ℝ`.  Expanding the square and summing over the points first (the corpus
duality expansion `dual_sum_expand`, with the pair `(t₁,t₂)` as summation index) gives the
ratio-kernel identity

`Σ_{t₁,t₂} |Σ_n a_n n^{i(t₁−t₂)}|² = Σ_{n,m} Re(a_n ā_m) · K(n,m)`,
`K(n,m) = |Σ_{t∈W} n^{it} m^{−it}|² = |R(n/m)|²`,  `R(v) = Σ_{t∈W} v^{it}` (`GuthMaynard.lagSum`),

the last form being Guth–Maynard's (proof of Lemma 11.5).  Since `K ≥ 0`, the **majorant principle**
follows: `|a_n| ≤ b_n` implies that the pair sum of `a` is at most that of `b`.  (The uniform case
`b_n ≡ A` is Jutila's coefficient removal `jutila_coefficient_removal`.)  For nonnegative real
coefficients the pair sum is monotone in the support, scales quadratically, and does not see a
common shift `t₁ − t₂ ↦ t₁ − t₂ + u` after the majorant step.

The phase is the one of the corpus `dirPoly`, and `hbPoly_eq_dirPoly` identifies a polynomial on
a support inside `[1, L]` with `dirPoly L` of the zero-extended coefficient vector.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset ComplexConjugate

noncomputable section

/-- The phase `n^{it} = e^{it log n}`. -/
def hbPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I)

/-- The Dirichlet polynomial `Σ_{n∈S} a_n n^{it}`. -/
def hbPoly (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * hbPhase n t

/-- Heath-Brown's pair sum `Σ_{t₁,t₂∈W} |Σ_{n∈S} a_n n^{i(t₁−t₂)}|²`. -/
def hbPairSum (W : Finset ℝ) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ 2

/-- The ratio kernel `K(n,m) = |Σ_{t∈W} n^{it} m^{−it}|²`. -/
def hbKernel (W : Finset ℝ) (n m : ℕ) : ℝ :=
  ‖∑ t ∈ W, hbPhase n t * conj (hbPhase m t)‖ ^ 2

/-! ### The phase -/

theorem norm_hbPhase (n : ℕ) (t : ℝ) : ‖hbPhase n t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hbPhase_add (n : ℕ) (s t : ℝ) : hbPhase n (s + t) = hbPhase n s * hbPhase n t := by
  rw [hbPhase, hbPhase, hbPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_hbPhase (n : ℕ) (t : ℝ) : conj (hbPhase n t) = hbPhase n (-t) := by
  rw [hbPhase, hbPhase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem hbPhase_sub (n : ℕ) (s t : ℝ) :
    hbPhase n (s - t) = hbPhase n s * conj (hbPhase n t) := by
  rw [conj_hbPhase, ← hbPhase_add, sub_eq_add_neg]

theorem hbPhase_zero_right (n : ℕ) : hbPhase n 0 = 1 := by
  simp [hbPhase]

/-- `|n^{it}|² = 1`, in the form `n^{it} · conj(n^{it}) = 1`. -/
theorem hbPhase_mul_conj_self (n : ℕ) (t : ℝ) : hbPhase n t * conj (hbPhase n t) = 1 := by
  rw [Complex.mul_conj', norm_hbPhase]
  simp

/-- Complete multiplicativity of the phase on positive integers. -/
theorem hbPhase_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (t : ℝ) :
    hbPhase (n * m) t = hbPhase n t * hbPhase m t := by
  rw [hbPhase, hbPhase, hbPhase, ← Complex.exp_add, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hm)]
  congr 1
  push_cast
  ring

/-- `n^{it} m^{−it} = (n/m)^{it}` for positive integers. -/
theorem hbPhase_mul_conj_eq_ratio {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (t : ℝ) :
    hbPhase n t * conj (hbPhase m t) =
      Complex.exp (((t * Real.log ((n : ℝ) / m) : ℝ) : ℂ) * Complex.I) := by
  rw [conj_hbPhase, hbPhase, hbPhase, ← Complex.exp_add,
    Real.log_div (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hm)]
  congr 1
  push_cast
  ring

/-! ### The polynomial -/

/-- Scalars pull out of the polynomial. -/
theorem hbPoly_const_mul (S : Finset ℕ) (a : ℕ → ℂ) (c : ℂ) (t : ℝ) :
    hbPoly S (fun n => c * a n) t = c * hbPoly S a t := by
  rw [hbPoly, hbPoly, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- A shift of the argument is a unimodular twist of the coefficients. -/
theorem hbPoly_add (S : Finset ℕ) (a : ℕ → ℂ) (t u : ℝ) :
    hbPoly S a (t + u) = hbPoly S (fun n => a n * hbPhase n u) t := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hbPhase_add]
  ring

/-- Zero-extension: a polynomial on `S ⊆ S'` is the polynomial on `S'` with coefficients
vanishing off `S`. -/
theorem hbPoly_eq_ite_of_subset {S S' : Finset ℕ} (hSS' : S ⊆ S') (a : ℕ → ℂ) (t : ℝ) :
    hbPoly S a t = hbPoly S' (fun n => if n ∈ S then a n else 0) t := by
  simp only [hbPoly, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSS']

/-- The polynomial at the origin is the coefficient sum. -/
theorem hbPoly_zero (S : Finset ℕ) (a : ℕ → ℂ) : hbPoly S a 0 = ∑ n ∈ S, a n := by
  simp [hbPoly, hbPhase_zero_right]

/-- Reindexing `Fin L` as `{1, …, L}`. -/
theorem sum_fin_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (L : ℕ) (f : ℕ → M) :
    ∑ i : Fin L, f ((i : ℕ) + 1) = ∑ n ∈ Finset.Icc 1 L, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) L, Finset.range_eq_Ico,
    Finset.sum_Ico_add' f 0 L 1, zero_add]
  rfl

/-- **Bridge to the corpus `dirPoly`.**  A polynomial supported in `[1, L]` is `dirPoly L` of
its zero-extended coefficient vector (index `i` carries `n = i + 1`). -/
theorem hbPoly_eq_dirPoly {S : Finset ℕ} {L : ℕ} (hS : S ⊆ Finset.Icc 1 L) (a : ℕ → ℂ)
    (t : ℝ) :
    hbPoly S a t = dirPoly L (fun i => if (i : ℕ) + 1 ∈ S then a ((i : ℕ) + 1) else 0) t := by
  rw [hbPoly_eq_ite_of_subset hS, dirPoly, hbPoly,
    ← sum_fin_succ_eq_sum_Icc L (fun n => (if n ∈ S then a n else 0) * hbPhase n t)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbPhase]
  push_cast
  rfl

/-- **Reverse bridge.**  `dirPoly L c` is the polynomial on `[1, L]` whose coefficient at `n`
is `c (n − 1)`. -/
theorem dirPoly_eq_hbPoly (L : ℕ) (c : Fin L → ℂ) (t : ℝ) :
    dirPoly L c t =
      hbPoly (Finset.Icc 1 L) (fun n => if h : n - 1 < L then c ⟨n - 1, h⟩ else 0) t := by
  rw [hbPoly, ← sum_fin_succ_eq_sum_Icc L
    (fun n => (if h : n - 1 < L then c ⟨n - 1, h⟩ else 0) * hbPhase n t), dirPoly]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) + 1 - 1 < L := by simp
  rw [dif_pos hi, hbPhase]
  push_cast
  simp

/-! ### The ratio-kernel identity -/

/-- `Σ_{(t₁,t₂)∈W²} x(t₁) conj(x(t₂)) = |Σ_{t∈W} x(t)|²`. -/
private theorem sum_product_mul_conj (W : Finset ℝ) (x : ℝ → ℂ) :
    ∑ p ∈ W ×ˢ W, x p.1 * conj (x p.2) = ((‖∑ t ∈ W, x t‖ ^ 2 : ℝ) : ℂ) := by
  rw [Finset.sum_product]
  dsimp only
  rw [← Finset.sum_mul_sum, ← map_sum, Complex.mul_conj']
  push_cast
  rfl

theorem hbKernel_nonneg (W : Finset ℝ) (n m : ℕ) : 0 ≤ hbKernel W n m := by
  unfold hbKernel
  positivity

theorem hbPairSum_nonneg (W : Finset ℝ) (S : Finset ℕ) (a : ℕ → ℂ) : 0 ≤ hbPairSum W S a := by
  unfold hbPairSum
  positivity

/-- **The ratio-kernel identity.**
`Σ_{t₁,t₂∈W} |Σ_n a_n n^{i(t₁−t₂)}|² = Σ_{n,m} Re(a_n ā_m) |Σ_{t∈W} n^{it} m^{−it}|²`. -/
theorem hbPairSum_eq_sum_kernel (W : Finset ℝ) (S : Finset ℕ) (a : ℕ → ℂ) :
    hbPairSum W S a = ∑ n ∈ S, ∑ m ∈ S, (a n * conj (a m)).re * hbKernel W n m := by
  have h := GaloisForLFunctions.dual_sum_expand (ι := S) (κ := ↥(W ×ˢ W))
    (M := fun i p => hbPhase i (p : ℝ × ℝ).1 * conj (hbPhase i (p : ℝ × ℝ).2)) (fun i => a i)
  have hL : hbPairSum W S a = ∑ p : ↥(W ×ˢ W),
      ‖∑ i : S, a i * (hbPhase i (p : ℝ × ℝ).1 * conj (hbPhase i (p : ℝ × ℝ).2))‖ ^ 2 := by
    rw [Finset.sum_coe_sort (W ×ˢ W)
      (fun p => ‖∑ i : S, a i * (hbPhase i p.1 * conj (hbPhase i p.2))‖ ^ 2),
      Finset.sum_product, hbPairSum]
    refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
    rw [hbPoly, ← Finset.sum_coe_sort S]
    simp only [hbPhase_sub]
  rw [hL, h, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hZ : ∑ p : ↥(W ×ˢ W), hbPhase i (p : ℝ × ℝ).1 * conj (hbPhase i (p : ℝ × ℝ).2) *
      conj (hbPhase j (p : ℝ × ℝ).1 * conj (hbPhase j (p : ℝ × ℝ).2)) =
        ((hbKernel W i j : ℝ) : ℂ) := by
    rw [hbKernel, ← sum_product_mul_conj, ← Finset.sum_coe_sort (W ×ˢ W)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hZ, Complex.re_mul_ofReal]

/-- The kernel is Guth–Maynard's `|R(n/m)|²`, `R = GuthMaynard.lagSum W`. -/
theorem hbKernel_eq_normSq_lagSum (W : Finset ℝ) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    hbKernel W n m = ‖GuthMaynard.lagSum W ((n : ℝ) / m)‖ ^ 2 := by
  rw [hbKernel, GuthMaynard.lagSum]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hbPhase_mul_conj_eq_ratio hn hm]
  congr 1
  push_cast
  ring

/-- **Guth–Maynard, proof of Lemma 11.5.**
`Σ_{n,m∈S} |R(n/m)|² = Σ_{t₁,t₂∈W} |Σ_{n∈S} n^{i(t₁−t₂)}|²` for `0 ∉ S`. -/
theorem sum_normSq_lagSum_eq_hbPairSum (W : Finset ℝ) {S : Finset ℕ} (hS : (0 : ℕ) ∉ S) :
    ∑ n ∈ S, ∑ m ∈ S, ‖GuthMaynard.lagSum W ((n : ℝ) / m)‖ ^ 2 =
      hbPairSum W S (fun _ => 1) := by
  rw [hbPairSum_eq_sum_kernel]
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
  rw [hbKernel_eq_normSq_lagSum W (ne_of_mem_of_not_mem hn hS) (ne_of_mem_of_not_mem hm hS)]
  simp

/-- The identity for real coefficients: `Σ_{n,m} b_n b_m K(n,m)`. -/
theorem hbPairSum_ofReal (W : Finset ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    hbPairSum W S (fun n => (b n : ℂ)) = ∑ n ∈ S, ∑ m ∈ S, b n * b m * hbKernel W n m := by
  rw [hbPairSum_eq_sum_kernel]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ### The majorant principle and its consequences -/

/-- **The majorant principle** (Heath-Brown; Lemma 2.1 of the Warwick notes).  If
`|a_n| ≤ b_n` on `S`, the pair sum of `a` is at most the pair sum of `b`. -/
theorem hbPairSum_le_of_norm_le (W : Finset ℝ) {S : Finset ℕ} {a : ℕ → ℂ} {b : ℕ → ℝ}
    (hab : ∀ n ∈ S, ‖a n‖ ≤ b n) : hbPairSum W S a ≤ hbPairSum W S (fun n => (b n : ℂ)) := by
  rw [hbPairSum_eq_sum_kernel, hbPairSum_ofReal]
  refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
  refine mul_le_mul_of_nonneg_right ?_ (hbKernel_nonneg W n m)
  calc (a n * conj (a m)).re ≤ ‖a n * conj (a m)‖ := Complex.re_le_norm _
    _ = ‖a n‖ * ‖a m‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ b n * b m := mul_le_mul (hab n hn) (hab m hm) (norm_nonneg _)
          ((norm_nonneg _).trans (hab n hn))

/-- A scalar factor `c` of the coefficients costs `|c|²`. -/
theorem hbPairSum_const_mul (W : Finset ℝ) (S : Finset ℕ) (a : ℕ → ℂ) (c : ℂ) :
    hbPairSum W S (fun n => c * a n) = ‖c‖ ^ 2 * hbPairSum W S a := by
  simp only [hbPairSum, hbPoly_const_mul, norm_mul, mul_pow, Finset.mul_sum]

/-- For nonnegative real coefficients the pair sum is monotone in the support. -/
theorem hbPairSum_ofReal_mono_support (W : Finset ℝ) {S S' : Finset ℕ} (hSS' : S ⊆ S')
    {b : ℕ → ℝ} (hb : ∀ n ∈ S', 0 ≤ b n) :
    hbPairSum W S (fun n => (b n : ℂ)) ≤ hbPairSum W S' (fun n => (b n : ℂ)) := by
  rw [hbPairSum_ofReal, hbPairSum_ofReal]
  have hterm : ∀ n ∈ S', ∀ m ∈ S', 0 ≤ b n * b m * hbKernel W n m := fun n hn m hm =>
    mul_nonneg (mul_nonneg (hb n hn) (hb m hm)) (hbKernel_nonneg W n m)
  calc ∑ n ∈ S, ∑ m ∈ S, b n * b m * hbKernel W n m
      ≤ ∑ n ∈ S, ∑ m ∈ S', b n * b m * hbKernel W n m :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum_of_subset_of_nonneg hSS'
          fun m hm _ => hterm n (hSS' hn) m hm
    _ ≤ ∑ n ∈ S', ∑ m ∈ S', b n * b m * hbKernel W n m :=
        Finset.sum_le_sum_of_subset_of_nonneg hSS' fun n hn _ =>
          Finset.sum_nonneg fun m hm => hterm n hn m hm

/-- **The shift is invisible after the majorant step.**  For every real `u`,
`Σ_{t₁,t₂} |Σ_n a_n n^{i(t₁−t₂+u)}|² ≤ Σ_{t₁,t₂} |Σ_n b_n n^{i(t₁−t₂)}|²` when `|a_n| ≤ b_n`. -/
theorem sum_normSq_hbPoly_shift_le (W : Finset ℝ) {S : Finset ℕ} {a : ℕ → ℂ} {b : ℕ → ℝ}
    (hab : ∀ n ∈ S, ‖a n‖ ≤ b n) (u : ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂ + u)‖ ^ 2 ≤
      hbPairSum W S (fun n => (b n : ℂ)) := by
  have htw : ∀ n ∈ S, ‖a n * hbPhase n u‖ ≤ b n := fun n hn => by
    rw [norm_mul, norm_hbPhase, mul_one]
    exact hab n hn
  calc ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂ + u)‖ ^ 2
      = hbPairSum W S (fun n => a n * hbPhase n u) := by
        simp only [hbPairSum, hbPoly_add]
    _ ≤ _ := hbPairSum_le_of_norm_le W htw

/-- **Diagonal split.**  The pairs `t₁ = t₂` contribute `|W| · |Σ_n a_n|²`. -/
theorem hbPairSum_eq_diag_add_offDiag (W : Finset ℝ) (S : Finset ℕ) (a : ℕ → ℂ) :
    hbPairSum W S a = (W.card : ℝ) * ‖∑ n ∈ S, a n‖ ^ 2 +
      ∑ t₁ ∈ W, ∑ t₂ ∈ W.erase t₁, ‖hbPoly S a (t₁ - t₂)‖ ^ 2 := by
  have hrow : ∀ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ 2 =
      ‖∑ n ∈ S, a n‖ ^ 2 + ∑ t₂ ∈ W.erase t₁, ‖hbPoly S a (t₁ - t₂)‖ ^ 2 := by
    intro t₁ ht₁
    rw [← Finset.add_sum_erase _ _ ht₁, sub_self, hbPoly_zero]
  rw [hbPairSum, Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul]

end

end RHTower.Sieve
