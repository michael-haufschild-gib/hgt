import GaloisForLFunctions.RHTower.PrimePowerSumBound

/-!
# Unweighted prime shells

The card's `(12)` averages over primes, not over the logarithmic prime mass.  On a shell `(a, b]`
with `a > 1` the two differ by at most the ratio `log b / log a`, because every prime of the shell
has `log a < log p ≤ log b`.  So the Chebyshev mass again controls everything.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The unweighted prime sum over the shell `(a, b]`. -/
def primeCountSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p), f p

/-- The number of primes of the shell. -/
def primeShellCard (a b : ℝ) : ℕ :=
  ((Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p)).card

theorem primeCountSum_const (a b : ℝ) (M : ℝ) :
    primeCountSum (fun _ => M) a b = (primeShellCard a b : ℝ) * M := by
  rw [primeCountSum, Finset.sum_const, primeShellCard, nsmul_eq_mul]

/-- **The shell count is controlled by the Chebyshev mass.** -/
theorem primeShellCard_bounds {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (Chebyshev.theta b - Chebyshev.theta a) / Real.log b ≤ (primeShellCard a b : ℝ)
      ∧ (primeShellCard a b : ℝ) ≤ (Chebyshev.theta b - Chebyshev.theta a) / Real.log a := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  have hb1 : (1 : ℝ) < b := lt_of_lt_of_le ha hab
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hmass := chebyshevTheta_sub_eq_shellSum (x := a) (y := b) hfl
  constructor
  · rw [div_le_iff₀ hlb, hmass]
    have : ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p), Real.log p
        ≤ ∑ _p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p), Real.log b := by
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨-, -, h2⟩ := mem_shell_of_mem_filter ha0.le hp
      exact Real.log_le_log (by
        have : (0 : ℝ) < a := ha0
        linarith [(mem_shell_of_mem_filter ha0.le hp).2.1]) h2
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  · rw [le_div_iff₀ hla, hmass]
    have : ∑ _p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p), Real.log a
        ≤ ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p), Real.log p := by
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨-, h1, -⟩ := mem_shell_of_mem_filter ha0.le hp
      exact Real.log_le_log ha0 h1.le
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this

/-- **The upper sandwich for an unweighted shell sum.** -/
theorem primeCountSum_le {f : ℝ → ℝ} {a b M : ℝ} (ha : 1 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ p : ℕ, Nat.Prime p → a < (p : ℝ) → (p : ℝ) ≤ b → f p ≤ M) :
    primeCountSum f a b ≤ (primeShellCard a b : ℝ) * M := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  rw [← primeCountSum_const a b M]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hprime, h1, h2⟩ := mem_shell_of_mem_filter ha0.le hp
  exact hf p hprime h1 h2

/-- **The lower sandwich for an unweighted shell sum.** -/
theorem le_primeCountSum {f : ℝ → ℝ} {a b m : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hf : ∀ p : ℕ, Nat.Prime p → a < (p : ℝ) → (p : ℝ) ≤ b → m ≤ f p) :
    (primeShellCard a b : ℝ) * m ≤ primeCountSum f a b := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  rw [← primeCountSum_const a b m]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hprime, h1, h2⟩ := mem_shell_of_mem_filter ha0.le hp
  exact hf p hprime h1 h2

/-- Unweighted shells add. -/
theorem primeCountSum_add {f : ℝ → ℝ} {a b c : ℝ} (hab : ⌊a⌋₊ ≤ ⌊b⌋₊) (hbc : ⌊b⌋₊ ≤ ⌊c⌋₊) :
    primeCountSum f a b + primeCountSum f b c = primeCountSum f a c := by
  classical
  have hunion : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ∪ Finset.Ioc ⌊b⌋₊ ⌊c⌋₊ = Finset.Ioc ⌊a⌋₊ ⌊c⌋₊ :=
    Finset.Ioc_union_Ioc_eq_Ioc hab hbc
  have hdisj : Disjoint (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) (Finset.Ioc ⌊b⌋₊ ⌊c⌋₊) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have h1 := (Finset.mem_Ioc.mp hp).2
    have h2 := (Finset.mem_Ioc.mp hp').1
    omega
  rw [primeCountSum, primeCountSum, primeCountSum, ← hunion, Finset.filter_union,
    Finset.sum_union (Finset.disjoint_filter_filter hdisj)]

/-- Unweighted shells chain. -/
theorem primeCountSum_chain (f : ℝ → ℝ) (x : ℕ → ℝ)
    (hmono : ∀ k, ⌊x k⌋₊ ≤ ⌊x (k + 1)⌋₊) (n : ℕ) :
    ∑ k ∈ Finset.range n, primeCountSum f (x k) (x (k + 1)) = primeCountSum f (x 0) (x n) := by
  have hmono0 : ∀ m : ℕ, ⌊x 0⌋₊ ≤ ⌊x m⌋₊ := by
    intro m
    induction m with
    | zero => exact le_rfl
    | succ k ihk => exact le_trans ihk (hmono k)
  induction n with
  | zero => simp [primeCountSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact primeCountSum_add (hmono0 n) (hmono n)

end

end RHTower
