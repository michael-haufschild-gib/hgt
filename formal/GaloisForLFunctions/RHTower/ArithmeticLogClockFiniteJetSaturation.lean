import GaloisForLFunctions.RHTower.ArithmeticSchurFirstTraceNonclosability
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Universal finite-jet saturation of the actual-prime logarithmic clock

Let `k_p = (1, p⁻¹, p⁻², ...)` be the normalized arithmetic-Schur Hardy kernel.  Removing
the first `m` Taylor coordinates from `(log p) k_p` and shifting the remaining tail back to
degree zero gives `(log p) p⁻ᵐ k_p`.  This module proves, for every finite `m`, that the graph
of this clock on finitely supported actual-prime packets is dense in the full product of its
two Hardy pivots.

Thus no finite Taylor/principal-trace renormalization makes the prime-log clock closable.  The
result is stronger than one graph-null sequence: every horizontal and every shifted vertical
Hardy direction occurs in the graph closure.  The proof is a logarithmic-germ rigidity law.
A joint annihilator would satisfy

`F_x(1/p) + (log p) p⁻ᵐ F_y(1/p) = 0`

for every prime.  Successive Hardy backward shifts first remove the `m` finite Taylor
coordinates; the remaining logarithmic relation forces both germs to vanish coefficient by
coefficient.  `hardyPrependZero_comp_primeFiniteTraceClock_one` identifies order one with the
previously formalized actual first-trace clock exactly.

No Xi zero, RH assumption, numerical computation, or nonstandard axiom is used.
-/


open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

def hardyDrop : PrimeHardy →ₗ[ℝ] PrimeHardy where
  toFun x := ⟨fun n => x (n + 1), by
    apply memℓp_gen
    have hs : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) :=
      x.2.summable (by norm_num)
    simpa only [ENNReal.toReal_ofNat] using (summable_nat_add_iff 1).2 hs⟩
  map_add' x y := by ext n; rfl
  map_smul' c x := by ext n; rfl

@[simp] theorem hardyDrop_apply (x : PrimeHardy) (n : ℕ) :
    hardyDrop x n = x (n + 1) := rfl

theorem inner_hardyKernel_recurrence (q : ℝ) (hq : |q| < 1) (x : PrimeHardy) :
    inner ℝ (hardyKernel q hq) x = x 0 + q * inner ℝ (hardyKernel q hq) (hardyDrop x) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hs : Summable (fun i : ℕ =>
      inner ℝ (hardyKernel q hq i) (x i)) :=
    lp.summable_inner (𝕜 := ℝ) (hardyKernel q hq) x
  have hsplit := hs.sum_add_tsum_nat_add 1
  simp only [hardyKernel_apply, RCLike.inner_apply, conj_trivial, hardyDrop_apply] at hsplit ⊢
  calc
    (∑' i : ℕ, x i * q ^ i) =
        x 0 + ∑' i : ℕ, x (i + 1) * q ^ (i + 1) := by
      simpa using hsplit.symm
    _ = x 0 + q * ∑' i : ℕ, x (i + 1) * q ^ i := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [pow_succ]
      ring

theorem tendsto_primeReciprocal_nthPrimePoint_zero :
    Tendsto (fun n => primeReciprocal (nthPrimePoint n)) atTop (𝓝 0) := by
  simpa [primeReciprocal] using!
    (tendsto_inv_atTop_zero.comp tendsto_nthPrimePoint_cast_atTop)

theorem tendsto_log_nthPrimePoint_atTop :
    Tendsto (fun n => Real.log ((nthPrimePoint n).1 : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_nthPrimePoint_cast_atTop

theorem tendsto_log_mul_primeReciprocal_nthPrimePoint_zero :
    Tendsto (fun n => Real.log ((nthPrimePoint n).1 : ℝ) *
      primeReciprocal (nthPrimePoint n)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_nthPrimePoint_cast_atTop
  simpa [primeReciprocal, div_eq_mul_inv] using! h

theorem tendsto_primeLogTailWeight_succ_zero (m : ℕ) :
    Tendsto (fun n => Real.log ((nthPrimePoint n).1 : ℝ) *
      primeReciprocal (nthPrimePoint n) ^ (m + 1)) atTop (𝓝 0) := by
  have hqpow := tendsto_primeReciprocal_nthPrimePoint_zero.pow m
  have h := tendsto_log_mul_primeReciprocal_nthPrimePoint_zero.mul hqpow
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem tendsto_primeHardyKernel_nthPrimePoint_vacuum :
    Tendsto (fun n => primeHardyKernel (nthPrimePoint n)) atTop (𝓝 hardyVacuum) := by
  have hinv := tendsto_primeReciprocal_nthPrimePoint_zero
  have hbound : Tendsto (fun n => 2 * primeReciprocal (nthPrimePoint n))
      atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hinv
  have htail : Tendsto (fun n => primeHardyTail (nthPrimePoint n)) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hevent : ∀ᶠ n : ℕ in atTop,
        2 * primeReciprocal (nthPrimePoint n) < ε :=
      (tendsto_order.1 hbound).2 ε hε
    filter_upwards [hevent] with n hn
    exact lt_of_le_of_lt (by
      simpa [primeReciprocal, div_eq_mul_inv] using
        norm_primeHardyTail_le (nthPrimePoint n)) hn
  have h := htail.add_const hardyVacuum
  simpa [primeHardyTail, hardyFirstTail, primeHardyKernel] using h

theorem inner_hardyVacuum (x : PrimeHardy) : inner ℝ hardyVacuum x = x 0 := by
  rw [hardyVacuum, lp.inner_single_left]
  simp [RCLike.inner_apply]

theorem tendsto_inner_primeHardyKernel_nthPrimePoint (x : PrimeHardy) :
    Tendsto (fun n => inner ℝ (primeHardyKernel (nthPrimePoint n)) x)
      atTop (𝓝 (x 0)) := by
  have h := Filter.Tendsto.inner (𝕜 := ℝ)
    tendsto_primeHardyKernel_nthPrimePoint_vacuum
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  simpa [inner_hardyVacuum] using h

def PrimeTailLogRelation (m : ℕ) (x y : PrimeHardy) : Prop :=
  ∀ p : Nat.Primes,
    inner ℝ (primeHardyKernel p) x +
      (Real.log (p.1 : ℝ) * primeReciprocal p ^ m) *
        inner ℝ (primeHardyKernel p) y = 0

theorem primeTailLogRelation_succ_head_zero {m : ℕ} {x y : PrimeHardy}
    (h : PrimeTailLogRelation (m + 1) x y) : x 0 = 0 := by
  have hX := tendsto_inner_primeHardyKernel_nthPrimePoint x
  have hY := tendsto_inner_primeHardyKernel_nthPrimePoint y
  have hw := tendsto_primeLogTailWeight_succ_zero m
  have hprod := hw.mul hY
  have hsum := hX.add hprod
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have heq : (fun n => inner ℝ (primeHardyKernel (nthPrimePoint n)) x +
      (Real.log ((nthPrimePoint n).1 : ℝ) *
        primeReciprocal (nthPrimePoint n) ^ (m + 1)) *
          inner ℝ (primeHardyKernel (nthPrimePoint n)) y) = fun _ => 0 := by
    funext n
    exact h (nthPrimePoint n)
  have : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (x 0 + 0)) := by
    simpa [heq] using hsum
  have hx : x 0 + 0 = 0 := tendsto_nhds_unique this hzero
  simpa using hx

theorem primeTailLogRelation_succ_drop {m : ℕ} {x y : PrimeHardy}
    (h : PrimeTailLogRelation (m + 1) x y) :
    PrimeTailLogRelation m (hardyDrop x) y := by
  have hx0 := primeTailLogRelation_succ_head_zero h
  intro p
  have hrec := inner_hardyKernel_recurrence (primeReciprocal p)
    (primeReciprocal_abs_lt_one p) x
  change inner ℝ (primeHardyKernel p) x =
    x 0 + primeReciprocal p * inner ℝ (primeHardyKernel p) (hardyDrop x) at hrec
  rw [hx0, zero_add] at hrec
  have hq0 : primeReciprocal p ≠ 0 := ne_of_gt (primeReciprocal_pos p)
  have hp := h p
  rw [hrec, pow_succ] at hp
  apply (mul_left_cancel₀ hq0)
  simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hp

theorem primeTailLogRelation_zero_heads {x y : PrimeHardy}
    (h : PrimeTailLogRelation 0 x y) : x 0 = 0 ∧ y 0 = 0 := by
  have hX := tendsto_inner_primeHardyKernel_nthPrimePoint x
  have hY := tendsto_inner_primeHardyKernel_nthPrimePoint y
  have hlog := tendsto_log_nthPrimePoint_atTop
  have hXdiv : Tendsto (fun n =>
      inner ℝ (primeHardyKernel (nthPrimePoint n)) x /
        Real.log ((nthPrimePoint n).1 : ℝ)) atTop (𝓝 0) := by
    exact hX.div_atTop hlog
  have hYzero : Tendsto (fun n =>
      inner ℝ (primeHardyKernel (nthPrimePoint n)) y) atTop (𝓝 0) := by
    have heq : (fun n => inner ℝ (primeHardyKernel (nthPrimePoint n)) y) =
        fun n => -(inner ℝ (primeHardyKernel (nthPrimePoint n)) x /
          Real.log ((nthPrimePoint n).1 : ℝ)) := by
      funext n
      have hp := h (nthPrimePoint n)
      simp only [pow_zero, mul_one] at hp
      have hlog0 : Real.log ((nthPrimePoint n).1 : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (nthPrimePoint n).2.one_lt))
      field_simp [hlog0]
      linarith
    rw [heq]
    simpa using hXdiv.neg
  have hy0 : y 0 = 0 := tendsto_nhds_unique hY hYzero
  have hdropY := tendsto_inner_primeHardyKernel_nthPrimePoint (hardyDrop y)
  have hsmall := tendsto_log_mul_primeReciprocal_nthPrimePoint_zero.mul hdropY
  have hXzero : Tendsto (fun n =>
      inner ℝ (primeHardyKernel (nthPrimePoint n)) x) atTop (𝓝 0) := by
    have heq : (fun n => inner ℝ (primeHardyKernel (nthPrimePoint n)) x) =
        fun n => -(Real.log ((nthPrimePoint n).1 : ℝ) *
          primeReciprocal (nthPrimePoint n) *
            inner ℝ (primeHardyKernel (nthPrimePoint n)) (hardyDrop y)) := by
      funext n
      have hp := h (nthPrimePoint n)
      simp only [pow_zero, mul_one] at hp
      have hrec := inner_hardyKernel_recurrence
        (primeReciprocal (nthPrimePoint n))
        (primeReciprocal_abs_lt_one (nthPrimePoint n)) y
      change inner ℝ (primeHardyKernel (nthPrimePoint n)) y =
        y 0 + primeReciprocal (nthPrimePoint n) *
          inner ℝ (primeHardyKernel (nthPrimePoint n)) (hardyDrop y) at hrec
      rw [hy0, zero_add] at hrec
      rw [hrec] at hp
      linarith
    rw [heq]
    simpa using hsmall.neg
  have hx0 : x 0 = 0 := tendsto_nhds_unique hX hXzero
  exact ⟨hx0, hy0⟩

theorem primeTailLogRelation_zero_drop {x y : PrimeHardy}
    (h : PrimeTailLogRelation 0 x y) :
    PrimeTailLogRelation 0 (hardyDrop x) (hardyDrop y) := by
  obtain ⟨hx0, hy0⟩ := primeTailLogRelation_zero_heads h
  intro p
  have hrecx := inner_hardyKernel_recurrence (primeReciprocal p)
    (primeReciprocal_abs_lt_one p) x
  have hrecy := inner_hardyKernel_recurrence (primeReciprocal p)
    (primeReciprocal_abs_lt_one p) y
  change inner ℝ (primeHardyKernel p) x =
    x 0 + primeReciprocal p * inner ℝ (primeHardyKernel p) (hardyDrop x) at hrecx
  change inner ℝ (primeHardyKernel p) y =
    y 0 + primeReciprocal p * inner ℝ (primeHardyKernel p) (hardyDrop y) at hrecy
  rw [hx0, zero_add] at hrecx
  rw [hy0, zero_add] at hrecy
  have hp := h p
  simp only [pow_zero, mul_one] at hp ⊢
  rw [hrecx, hrecy] at hp
  have hq0 : primeReciprocal p ≠ 0 := ne_of_gt (primeReciprocal_pos p)
  apply (mul_left_cancel₀ hq0)
  simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hp

def hardyDropN : ℕ → PrimeHardy →ₗ[ℝ] PrimeHardy
  | 0 => LinearMap.id
  | n + 1 => (hardyDropN n).comp hardyDrop

@[simp] theorem hardyDropN_apply (n k : ℕ) (x : PrimeHardy) :
    hardyDropN n x k = x (k + n) := by
  induction n generalizing k x with
  | zero => simp [hardyDropN]
  | succ n ih =>
      change hardyDropN n (hardyDrop x) k = x (k + (n + 1))
      rw [ih, hardyDrop_apply]
      congr 1

theorem hardyDropN_drop_comm (n : ℕ) (x : PrimeHardy) :
    hardyDropN n (hardyDrop x) = hardyDrop (hardyDropN n x) := by
  ext k
  simp only [hardyDropN_apply, hardyDrop_apply]
  exact congrArg x (by omega)

theorem primeTailLogRelation_zero_dropN {x y : PrimeHardy}
    (h : PrimeTailLogRelation 0 x y) (n : ℕ) :
    PrimeTailLogRelation 0 (hardyDropN n x) (hardyDropN n y) := by
  induction n with
  | zero => simpa [hardyDropN] using h
  | succ n ih =>
      change PrimeTailLogRelation 0
        (hardyDropN n (hardyDrop x)) (hardyDropN n (hardyDrop y))
      rw [hardyDropN_drop_comm, hardyDropN_drop_comm]
      exact primeTailLogRelation_zero_drop ih

theorem primeTailLogRelation_zero_eq_zero {x y : PrimeHardy}
    (h : PrimeTailLogRelation 0 x y) : x = 0 ∧ y = 0 := by
  constructor
  · ext n
    have hz := (primeTailLogRelation_zero_heads
      (primeTailLogRelation_zero_dropN h n)).1
    simpa using hz
  · ext n
    have hz := (primeTailLogRelation_zero_heads
      (primeTailLogRelation_zero_dropN h n)).2
    simpa using hz

theorem primeTailLogRelation_drop_order {m : ℕ} {x y : PrimeHardy}
    (h : PrimeTailLogRelation m x y) :
    PrimeTailLogRelation 0 (hardyDropN m x) y := by
  induction m generalizing x with
  | zero => simpa [hardyDropN] using h
  | succ m ih =>
      have hd := primeTailLogRelation_succ_drop h
      simpa [hardyDropN] using ih hd

theorem primeTailLogRelation_head_zero_of_lt {m k : ℕ} {x y : PrimeHardy}
    (h : PrimeTailLogRelation m x y) (hk : k < m) : x k = 0 := by
  induction k generalizing m x with
  | zero =>
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      simpa using primeTailLogRelation_succ_head_zero (m := r) h
  | succ k ih =>
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_trans (Nat.zero_lt_succ k) hk))
      have hrk : k < r := by omega
      have hd : PrimeTailLogRelation r (hardyDrop x) y :=
        primeTailLogRelation_succ_drop (m := r) (by simpa [hr] using h)
      have hz := ih hd hrk
      simpa using hz

theorem primeTailLogRelation_eq_zero (m : ℕ) {x y : PrimeHardy}
    (h : PrimeTailLogRelation m x y) : x = 0 ∧ y = 0 := by
  have hdrop := primeTailLogRelation_drop_order h
  have hzero := primeTailLogRelation_zero_eq_zero hdrop
  have hhead : ∀ k < m, x k = 0 := by
    exact fun k hk => primeTailLogRelation_head_zero_of_lt h hk
  refine ⟨?_, hzero.2⟩
  ext n
  by_cases hn : n < m
  · simpa using hhead n hn
  · have hn' : m ≤ n := Nat.le_of_not_gt hn
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn'
    have hc := congrArg (fun z : PrimeHardy => z r) hzero.1
    simpa [add_comm] using hc

def primeFiniteTraceClock (m : ℕ) : (Nat.Primes →₀ ℝ) →ₗ[ℝ] PrimeHardy :=
  Finsupp.lsum ℝ (fun p => LinearMap.toSpanSingleton ℝ _
    ((Real.log (p.1 : ℝ) * primeReciprocal p ^ m) • primeHardyKernel p))

@[simp] theorem primeFiniteTraceClock_single (m : ℕ) (p : Nat.Primes) (c : ℝ) :
    primeFiniteTraceClock m (Finsupp.single p c) =
      c • ((Real.log (p.1 : ℝ) * primeReciprocal p ^ m) • primeHardyKernel p) := by
  simp [primeFiniteTraceClock]

def realLinearGraphSubmodule
    {D H₁ H₂ : Type*} [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (i : D →ₗ[ℝ] H₁) (A : D →ₗ[ℝ] H₂) :
    Submodule ℝ (WithLp 2 (H₁ × H₂)) :=
  LinearMap.range ((WithLp.linearEquiv 2 ℝ (H₁ × H₂)).symm.toLinearMap.comp (i.prod A))

theorem realLinearGraphSubmodule_closure_eq_top_of_annihilator
    {D H₁ H₂ : Type*} [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (i : D →ₗ[ℝ] H₁) (A : D →ₗ[ℝ] H₂)
    (hann : ∀ x : H₁, ∀ y : H₂,
      (∀ d : D, inner ℝ (i d) x + inner ℝ (A d) y = 0) → x = 0 ∧ y = 0) :
    (realLinearGraphSubmodule i A).topologicalClosure = ⊤ := by
  have horth : (realLinearGraphSubmodule i A)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hrel : ∀ d : D,
        inner ℝ (i d) z.ofLp.1 + inner ℝ (A d) z.ofLp.2 = 0 := by
      intro d
      have hd := hz (WithLp.toLp 2 (i d, A d)) ⟨d, rfl⟩
      simpa [WithLp.prod_inner_apply] using hd
    rcases hann z.ofLp.1 z.ofLp.2 hrel with ⟨hx, hy⟩
    apply WithLp.ofLp_injective 2
    exact Prod.ext hx hy
  calc
    (realLinearGraphSubmodule i A).topologicalClosure =
        (realLinearGraphSubmodule i A)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℝ (WithLp 2 (H₁ × H₂)))ᗮ := by rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- Every finite Taylor subtraction of the actual-prime logarithmic clock has maximally
multivalued graph closure: after shifting away the subtracted jet, the closure is the full
Hardy-product pivot. -/
theorem primeFiniteTraceClock_graphClosure_eq_top (m : ℕ) :
    (realLinearGraphSubmodule primeHardyKernelMap
      (primeFiniteTraceClock m)).topologicalClosure = ⊤ := by
  apply realLinearGraphSubmodule_closure_eq_top_of_annihilator
  intro x y h
  apply primeTailLogRelation_eq_zero m
  intro p
  have hp := h (Finsupp.single p 1)
  simpa [primeFiniteTraceClock_single, inner_smul_left] using hp

/-- **Bounded scalarization rigidity.** At every finite subtraction order, no nonzero pair of
bounded Hardy-pivot functionals can cancel the source and logarithmic clock columns. -/
theorem primeFiniteTraceClock_no_bounded_scalar_balance (m : ℕ)
    (F G : PrimeHardy →L[ℝ] ℝ)
    (h : ∀ d : Nat.Primes →₀ ℝ,
      F (primeHardyKernelMap d) + G (primeFiniteTraceClock m d) = 0) :
    F = 0 ∧ G = 0 := by
  let x : PrimeHardy := (InnerProductSpace.toDual ℝ PrimeHardy).symm F
  let y : PrimeHardy := (InnerProductSpace.toDual ℝ PrimeHardy).symm G
  have hrel : PrimeTailLogRelation m x y := by
    intro p
    have hp := h (Finsupp.single p 1)
    have hFx : inner ℝ (primeHardyKernel p) x = F (primeHardyKernel p) := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hGy : inner ℝ (primeHardyKernel p) y = G (primeHardyKernel p) := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    rw [hFx, hGy]
    simpa [primeFiniteTraceClock_single, map_smul] using hp
  obtain ⟨hx, hy⟩ := primeTailLogRelation_eq_zero m hrel
  constructor
  · apply ContinuousLinearMap.ext
    intro z
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := PrimeHardy)]
    simp [x, hx]
  · apply ContinuousLinearMap.ext
    intro z
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := PrimeHardy)]
    simp [y, hy]

def hardyPrependZeroVec (x : PrimeHardy) : PrimeHardy :=
  ⟨fun n => match n with
      | 0 => 0
      | k + 1 => x k, by
    apply memℓp_gen
    rw [← summable_nat_add_iff 1]
    simpa only [ENNReal.toReal_ofNat] using x.2.summable (by norm_num)⟩

@[simp] theorem hardyPrependZeroVec_apply_zero (x : PrimeHardy) :
    hardyPrependZeroVec x 0 = 0 := rfl

@[simp] theorem hardyPrependZeroVec_apply_succ (x : PrimeHardy) (n : ℕ) :
    hardyPrependZeroVec x (n + 1) = x n := rfl

theorem hardyPrependZeroVec_add (x y : PrimeHardy) :
    hardyPrependZeroVec (x + y) = hardyPrependZeroVec x + hardyPrependZeroVec y := by
  apply lp.ext
  funext n
  have hadd := congrFun (lp.coeFn_add (hardyPrependZeroVec x) (hardyPrependZeroVec y)) n
  rw [hadd]
  cases n with
  | zero => simp
  | succ n =>
      have hxy := congrFun (lp.coeFn_add x y) n
      simpa using hxy

theorem hardyPrependZeroVec_smul (c : ℝ) (x : PrimeHardy) :
    hardyPrependZeroVec (c • x) = c • hardyPrependZeroVec x := by
  apply lp.ext
  funext n
  have hsmul := congrFun (lp.coeFn_smul c (hardyPrependZeroVec x)) n
  rw [hsmul]
  cases n <;> simp

def hardyPrependZero : PrimeHardy →ₗ[ℝ] PrimeHardy where
  toFun := hardyPrependZeroVec
  map_add' := hardyPrependZeroVec_add
  map_smul' := hardyPrependZeroVec_smul

@[simp] theorem hardyPrependZero_apply_zero (x : PrimeHardy) :
    hardyPrependZero x 0 = 0 := rfl

@[simp] theorem hardyPrependZero_apply_succ (x : PrimeHardy) (n : ℕ) :
    hardyPrependZero x (n + 1) = x n := rfl

theorem hardyPrependZero_primeReciprocal_smul_kernel (p : Nat.Primes) :
    hardyPrependZero
        (primeReciprocal p • primeHardyKernel p) = primeHardyTail p := by
  ext n
  cases n with
  | zero =>
      exact (hardyFirstTail_apply_zero (primeReciprocal p)
        (primeReciprocal_abs_lt_one p)).symm
  | succ n =>
      rw [hardyPrependZero_apply_succ]
      simp [primeHardyKernel, primeHardyTail, hardyFirstTail_apply_succ,
        pow_succ, mul_comm]

/-- At order one, the universal finite-trace clock is exactly the previously formalized actual
first-trace clock after the canonical zero-prepending tail embedding. -/
theorem hardyPrependZero_comp_primeFiniteTraceClock_one :
    hardyPrependZero.comp (primeFiniteTraceClock 1) = primeFirstTraceClock := by
  apply LinearMap.ext
  intro f
  induction f using Finsupp.induction with
  | zero => simp
  | single_add p c f hp hc ih =>
      simp only [map_add, ih]
      congr 1
      simp only [LinearMap.comp_apply]
      rw [primeFiniteTraceClock_single, primeFirstTraceClock_single, map_smul]
      simp only [pow_one]
      rw [show (Real.log (p.1 : ℝ) * primeReciprocal p) • primeHardyKernel p =
          Real.log (p.1 : ℝ) • (primeReciprocal p • primeHardyKernel p) by
        simp [smul_smul]]
      rw [map_smul, hardyPrependZero_primeReciprocal_smul_kernel]

end

end RHTower
