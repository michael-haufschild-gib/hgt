import GaloisForLFunctions.ArithmeticCorrelationGeometry.FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot

/-!
# The additively invariant gauge point

A gauge point is a unimodular completely multiplicative function `χ_x` on the positive integers
(`ArithmeticCorrelationGeometry.twist`). The trivial point `x = 0` is the prime source itself. This
file shows that it is the only gauge point that sees addition: any trace of additive structure on a
nowhere-vanishing completely multiplicative function forces it to be identically one.

* **Eventual periodicity** (`eq_one_of_eventually_periodic`). If `f(n + q) = f(n)` for all large
  `n`, then `f(qk + q) = f(qk)` gives `f(k + 1) = f(k)` after cancelling `f(q)`; so `f` is eventually
  a constant `c`, and `f(K²) = f(K)²` forces `c = 1`; multiplicativity spreads this to every `n`.
* **Convergence** (`eq_one_of_tendsto`). If `f(n) → L ≠ 0`, then `f(mn) = f(m) f(n)` tends to both
  `L` and `f(m) L`, so `f(m) = 1`.
* **Gauge points** (`twist_eq_one_of_eventually_periodic`, `twist_eq_one_of_tendsto`). A twist that
  is eventually periodic or convergent is the trivial twist.
* **Dirichlet gauge points** (`dirichletCharacter_eq_one_of_periodic_gauge`). The gauge point of a
  Dirichlet character agrees with the character off its modulus; it is eventually periodic only for
  the trivial character. Dirichlet characters carry additive structure only because they vanish at
  the primes of their modulus, which no gauge point does.

So the special points of the gauge torus are not unimodular periodic functions: periodicity is
available only at `0`. The vertical shifts `n^{it}` are slowly varying but not convergent, and
remain gauge points.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- Complete multiplicativity on the positive integers. -/
def IsCompletelyMultiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n

theorem isCompletelyMultiplicative_twist (x : GaugeTorus) :
    IsCompletelyMultiplicative (twist x) :=
  fun _ _ hm hn => twist_mul x hm hn

theorem twist_ne_zero (x : GaugeTorus) (n : ℕ) : twist x n ≠ 0 := by
  intro h
  have := norm_twist x n
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-! ### Periodicity forces the trivial point -/

/-- Eventual periodicity of a nowhere-vanishing completely multiplicative function makes it
eventually invariant under the successor. -/
theorem succ_eq_of_eventually_periodic {f : ℕ → ℂ} (hf : IsCompletelyMultiplicative f)
    (hne : ∀ n, n ≠ 0 → f n ≠ 0) {q N : ℕ} (hq : q ≠ 0) (hper : ∀ n, N ≤ n → f (n + q) = f n)
    {k : ℕ} (hk : max N 1 ≤ k) : f (k + 1) = f k := by
  have hk1 : k ≠ 0 := by omega
  have hNk : N ≤ q * k := le_trans (le_of_max_le_left hk) (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hq))
  have h := hper (q * k) hNk
  rw [← Nat.mul_succ, hf q (k + 1) hq (Nat.succ_ne_zero k), hf q k hq hk1] at h
  exact mul_left_cancel₀ (hne q hq) h

/-- Eventual periodicity makes the function eventually constant. -/
theorem eventually_const_of_eventually_periodic {f : ℕ → ℂ} (hf : IsCompletelyMultiplicative f)
    (hne : ∀ n, n ≠ 0 → f n ≠ 0) {q N : ℕ} (hq : q ≠ 0) (hper : ∀ n, N ≤ n → f (n + q) = f n) :
    ∀ k, max N 1 ≤ k → f k = f (max N 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [succ_eq_of_eventually_periodic hf hne hq hper hk, ih]

/-- **The additively invariant point is unique.** A nowhere-vanishing completely multiplicative
function that is eventually periodic is identically one on the positive integers. -/
theorem eq_one_of_eventually_periodic {f : ℕ → ℂ} (hf : IsCompletelyMultiplicative f)
    (hne : ∀ n, n ≠ 0 → f n ≠ 0) {q N : ℕ} (hq : q ≠ 0) (hper : ∀ n, N ≤ n → f (n + q) = f n) :
    ∀ n, n ≠ 0 → f n = 1 := by
  set K := max N 1 with hKdef
  have hK : K ≠ 0 := by omega
  have hconst := eventually_const_of_eventually_periodic hf hne hq hper
  -- `f(K)² = f(K²) = f(K)`, so `f(K) = 1`.
  have hc : f K = 1 := by
    have h := hconst (K * K) (Nat.le_mul_of_pos_left K (Nat.pos_of_ne_zero hK))
    rw [hf K K hK hK] at h
    exact mul_left_cancel₀ (hne K hK) (h.trans (mul_one _).symm)
  intro n hn
  have h := hconst (n * K) (Nat.le_mul_of_pos_left K (Nat.pos_of_ne_zero hn))
  rwa [hf n K hn hK, hc, mul_one] at h

/-- Eventual successor invariance is the case `q = 1`. -/
theorem eq_one_of_eventually_succ_invariant {f : ℕ → ℂ} (hf : IsCompletelyMultiplicative f)
    (hne : ∀ n, n ≠ 0 → f n ≠ 0) {N : ℕ} (hsucc : ∀ n, N ≤ n → f (n + 1) = f n) :
    ∀ n, n ≠ 0 → f n = 1 :=
  eq_one_of_eventually_periodic hf hne one_ne_zero hsucc

/-! ### Convergence forces the trivial point -/

/-- **A convergent completely multiplicative function with nonzero limit is identically one.** -/
theorem eq_one_of_tendsto {f : ℕ → ℂ} (hf : IsCompletelyMultiplicative f) {L : ℂ} (hL : L ≠ 0)
    (hlim : Tendsto f atTop (𝓝 L)) : ∀ m, m ≠ 0 → f m = 1 := by
  intro m hm
  have hsub : Tendsto (fun n => f (m * n)) atTop (𝓝 L) :=
    hlim.comp (tendsto_id.const_mul_atTop' (Nat.pos_of_ne_zero hm))
  have hprod : Tendsto (fun n => f (m * n)) atTop (𝓝 (f m * L)) := by
    refine (hlim.const_mul (f m)).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (hf m n hm hn).symm
  have := tendsto_nhds_unique hprod hsub
  exact mul_right_cancel₀ hL (this.trans (one_mul L).symm)

/-- A unimodular completely multiplicative function that converges is identically one. -/
theorem eq_one_of_tendsto_of_norm {f : ℕ → ℂ} (hf : IsCompletelyMultiplicative f)
    (hnorm : ∀ n, n ≠ 0 → ‖f n‖ = 1) {L : ℂ} (hlim : Tendsto f atTop (𝓝 L)) :
    ∀ m, m ≠ 0 → f m = 1 := by
  have hL : ‖L‖ = 1 := by
    have h := (continuous_norm.tendsto L).comp hlim
    refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (hnorm n hn).symm
  exact eq_one_of_tendsto hf (norm_ne_zero_iff.mp (hL ▸ one_ne_zero)) hlim

/-! ### Gauge points -/

/-- **An eventually periodic twist is the trivial twist.** -/
theorem twist_eq_one_of_eventually_periodic (x : GaugeTorus) {q N : ℕ} (hq : q ≠ 0)
    (hper : ∀ n, N ≤ n → twist x (n + q) = twist x n) : ∀ n, n ≠ 0 → twist x n = 1 :=
  eq_one_of_eventually_periodic (isCompletelyMultiplicative_twist x)
    (fun n _ => twist_ne_zero x n) hq hper

/-- **A convergent twist is the trivial twist.** -/
theorem twist_eq_one_of_tendsto (x : GaugeTorus) {L : ℂ}
    (hlim : Tendsto (twist x) atTop (𝓝 L)) : ∀ n, n ≠ 0 → twist x n = 1 :=
  eq_one_of_tendsto_of_norm (isCompletelyMultiplicative_twist x)
    (fun n _ => norm_twist x n) hlim

/-- **No nontrivial Dirichlet character is a periodic gauge point.** If the twist of the gauge
point of `χ` is eventually periodic, then `χ` is trivial. -/
theorem dirichletCharacter_eq_one_of_periodic_gauge {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {r N : ℕ} (hr : r ≠ 0)
    (hper : ∀ n, N ≤ n → twist (dirichletGauge χ) (n + r) = twist (dirichletGauge χ) n) :
    χ = 1 := by
  have htriv := twist_eq_one_of_eventually_periodic (dirichletGauge χ) hr hper
  ext u
  -- A positive representative `n + q` of the unit `u`.
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (u : ZMod q)
  have hm : ((n + q : ℕ) : ZMod q) = u := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero, hn]
  have hcop : Nat.Coprime (n + q) q := by
    rw [← ZMod.isUnit_iff_coprime, hm]
    exact u.isUnit
  have hm0 : n + q ≠ 0 := by
    have := NeZero.ne q
    omega
  have h := twist_dirichletGauge χ hm0 hcop
  rw [htriv (n + q) hm0, hm] at h
  rw [MulChar.one_apply_coe]
  exact h.symm

end GaloisForLFunctions.ArithmeticGaugeTheory
