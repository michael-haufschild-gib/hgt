import GaloisForLFunctions.RHTower.XiMassShellPrimeMass

/-!
# Weighted prime shells

The prime-log-weighted sum of a function over a shell `(a, b]` is sandwiched between the extreme
values of the weight times the Chebyshev mass `θ(b) − θ(a)` of the shell.  This is the elementary
device that replaces Riemann–Stieltjes integration for a merely measurable weight: no smoothness,
no bounded variation, only monotonicity of the prime mass.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The prime-log-weighted sum of `f` over the shell `(a, b]`. -/
def primeLogSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p), Real.log p * f p

theorem mem_shell_of_mem_filter {a b : ℝ} (ha : 0 ≤ a) {p : ℕ}
    (hp : p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => Nat.Prime p)) :
    Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨h1, h2⟩, hprime⟩ := hp
  have h3 : 1 ≤ p := hprime.one_lt.le.trans' (by norm_num)
  have h4 : 1 ≤ ⌊b⌋₊ := le_trans h3 h2
  have hb0 : 0 ≤ b := by
    by_contra hneg
    rw [not_le] at hneg
    rw [Nat.floor_of_nonpos hneg.le] at h4
    omega
  exact ⟨hprime, (Nat.floor_lt ha).1 h1, (Nat.le_floor_iff hb0).1 h2⟩

theorem log_nonneg_of_prime {p : ℕ} (hp : Nat.Prime p) : 0 ≤ Real.log p := by
  have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  exact Real.log_nonneg this

/-- **The upper sandwich.** -/
theorem primeLogSum_le {f : ℝ → ℝ} {a b M : ℝ} (ha : 0 ≤ a) (hab : ⌊a⌋₊ ≤ ⌊b⌋₊)
    (hf : ∀ p : ℕ, Nat.Prime p → a < (p : ℝ) → (p : ℝ) ≤ b → f p ≤ M) :
    primeLogSum f a b ≤ M * (Chebyshev.theta b - Chebyshev.theta a) := by
  rw [chebyshevTheta_sub_eq_shellSum hab, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hprime, h1, h2⟩ := mem_shell_of_mem_filter ha hp
  have hlog := log_nonneg_of_prime hprime
  have := hf p hprime h1 h2
  nlinarith [hlog, this]

/-- **The lower sandwich.** -/
theorem le_primeLogSum {f : ℝ → ℝ} {a b m : ℝ} (ha : 0 ≤ a) (hab : ⌊a⌋₊ ≤ ⌊b⌋₊)
    (hf : ∀ p : ℕ, Nat.Prime p → a < (p : ℝ) → (p : ℝ) ≤ b → m ≤ f p) :
    m * (Chebyshev.theta b - Chebyshev.theta a) ≤ primeLogSum f a b := by
  rw [chebyshevTheta_sub_eq_shellSum hab, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hprime, h1, h2⟩ := mem_shell_of_mem_filter ha hp
  have hlog := log_nonneg_of_prime hprime
  have := hf p hprime h1 h2
  nlinarith [hlog, this]

/-- Shells add. -/
theorem primeLogSum_add {f : ℝ → ℝ} {a b c : ℝ} (hab : ⌊a⌋₊ ≤ ⌊b⌋₊) (hbc : ⌊b⌋₊ ≤ ⌊c⌋₊) :
    primeLogSum f a b + primeLogSum f b c = primeLogSum f a c := by
  classical
  have hunion : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ∪ Finset.Ioc ⌊b⌋₊ ⌊c⌋₊ = Finset.Ioc ⌊a⌋₊ ⌊c⌋₊ :=
    Finset.Ioc_union_Ioc_eq_Ioc hab hbc
  have hdisj : Disjoint (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) (Finset.Ioc ⌊b⌋₊ ⌊c⌋₊) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have h1 := (Finset.mem_Ioc.mp hp).2
    have h2 := (Finset.mem_Ioc.mp hp').1
    omega
  rw [primeLogSum, primeLogSum, primeLogSum, ← hunion, Finset.filter_union,
    Finset.sum_union (Finset.disjoint_filter_filter hdisj)]

/-- The nonnegativity of a shell sum with a nonnegative weight. -/
theorem primeLogSum_nonneg {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hf : ∀ p : ℕ, Nat.Prime p → a < (p : ℝ) → (p : ℝ) ≤ b → 0 ≤ f p) :
    0 ≤ primeLogSum f a b := by
  refine Finset.sum_nonneg fun p hp => ?_
  obtain ⟨hprime, h1, h2⟩ := mem_shell_of_mem_filter ha hp
  exact mul_nonneg (log_nonneg_of_prime hprime) (hf p hprime h1 h2)

end

end RHTower
