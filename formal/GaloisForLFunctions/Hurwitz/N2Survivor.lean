/-
# Hurwitz N=2 — the survivor non-rationality kill

After the quadratic filtration zeroes all but one quadratic coefficient, the N=2 descent ends at a row
relation `q(−n)·V_n + l(−n) = 0` for all large `n`, where `V_n` is the survivor's tail value (e.g.
`V_n = ζ(s, −n)`) whose finite difference is the non-integer power `V_n − V_{n−1} = η·n^{−s}`
(`HurwitzZeta.hzeta_neg_nat_diff`, `η = e^{−iπs} ≠ 0`).

If the survivor coefficient `q ∈ ℂ[a]` were nonzero, then for large `n` (`q(−n) ≠ 0`) the relation gives
`V_n = −l(−n)/q(−n)` — a **rational function of `n`**. Its finite difference is then a ratio of
polynomials in `n` (compose `q, l` with the involutions `−X` and `1−X`), so `η·n^{−s}` would be an
eventual polynomial ratio — contradicting `HurwitzNonRat.not_eventually_cpow_polyRatio` for `s ∉ ℤ`.
Hence `q = 0`. This is the decisive obstruction the N=2 survivor needs; it plugs into the descent with
`V_n` the survivor tail and `η` the `hzeta_neg_nat_diff` multiplier.
-/
import GaloisForLFunctions.Hurwitz.NonRationality

open Polynomial Filter Topology

namespace HurwitzN2Survivor

open HurwitzNonRat

/-- `q ≠ 0 ⟹ q.comp(−X) ≠ 0`: composition with the involution `−X` preserves nonzero-ness. -/
theorem comp_neg_ne_zero {q : ℂ[X]} (hq : q ≠ 0) : q.comp (-X) ≠ 0 := by
  intro h
  apply hq
  have hinv : (q.comp (-X)).comp (-X) = q := by
    rw [Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp, neg_neg, Polynomial.comp_X]
  rw [h, Polynomial.zero_comp] at hinv
  exact hinv.symm

/-- `q ≠ 0 ⟹ q.comp(1−X) ≠ 0`: composition with the involution `1−X` preserves nonzero-ness. -/
theorem comp_oneSub_ne_zero {q : ℂ[X]} (hq : q ≠ 0) : q.comp (1 - X) ≠ 0 := by
  intro h
  apply hq
  have hinvol : (1 - X : ℂ[X]).comp (1 - X) = X := by
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]; ring
  have hinv : (q.comp (1 - X)).comp (1 - X) = q := by
    rw [Polynomial.comp_assoc, hinvol, Polynomial.comp_X]
  rw [h, Polynomial.zero_comp] at hinv
  exact hinv.symm

/-- A nonzero polynomial is eventually nonzero along `ℕ` (cast to `ℂ`): `p(n)/n^{deg} → lead p ≠ 0`. -/
theorem eventually_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    ∀ᶠ n : ℕ in atTop, p.eval (n : ℂ) ≠ 0 := by
  have hld : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  filter_upwards [(tendsto_eval_div_pow_nat p).eventually_ne hld] with n hn hc
  apply hn; rw [hc, zero_div]

/-- **Survivor kill (`q = 0`).** A row relation `q(−n)·V_n + l(−n) = 0` (all large `n`) whose tail value
`V_n` has finite difference `V_n − V_{n−1} = η·n^{−s}` (`η ≠ 0`, `s ∉ ℤ`) forces the survivor coefficient
`q = 0`: otherwise `V_n` is rational in `n` and `η·n^{−s}` becomes an eventual polynomial ratio,
contradicting `not_eventually_cpow_polyRatio`. -/
theorem survivor_q_eq_zero {s : ℂ} (hs : ∀ k : ℤ, s ≠ (k : ℂ)) {η : ℂ} (hη : η ≠ 0)
    {q l : ℂ[X]} {V : ℕ → ℂ}
    (hdiff : ∀ n : ℕ, 1 ≤ n → V n - V (n - 1) = η * (n : ℂ) ^ (-s))
    (hrel : ∀ᶠ n : ℕ in atTop, q.eval (-(n : ℂ)) * V n + l.eval (-(n : ℂ)) = 0) :
    q = 0 := by
  by_contra hq
  set Q0 := q.comp (-X) with hQ0def
  set Q1 := q.comp (1 - X) with hQ1def
  set L0 := l.comp (-X) with hL0def
  set L1 := l.comp (1 - X) with hL1def
  have hQ0 : Q0 ≠ 0 := comp_neg_ne_zero hq
  have hQ1 : Q1 ≠ 0 := comp_oneSub_ne_zero hq
  set denom := Q0 * Q1 with hdenomdef
  set num := -(L0 * Q1) + L1 * Q0 with hnumdef
  set D := C η * denom with hDdef
  have hDne : D ≠ 0 := mul_ne_zero (by rwa [Ne, C_eq_zero]) (mul_ne_zero hQ0 hQ1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hrel
  -- the eventual polynomial-ratio identity for `n^{-s}`
  have heq : ∀ᶠ n : ℕ in atTop, (n : ℂ) ^ (-s) * D.eval (n : ℂ) = num.eval (n : ℂ) := by
    filter_upwards [eventually_eval_ne_zero hQ0, eventually_eval_ne_zero hQ1,
      eventually_ge_atTop (M + 1), eventually_ge_atTop 1] with n hQ0n hQ1n hnM hn1
    -- evaluations of the composed polynomials
    have hev0 : Q0.eval (n : ℂ) = q.eval (-(n : ℂ)) := by
      rw [hQ0def, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
    have hevL0 : L0.eval (n : ℂ) = l.eval (-(n : ℂ)) := by
      rw [hL0def, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
    have hcast : -((n - 1 : ℕ) : ℂ) = 1 - (n : ℂ) := by
      rw [Nat.cast_sub hn1]; push_cast; ring
    have hev1 : Q1.eval (n : ℂ) = q.eval (-((n - 1 : ℕ) : ℂ)) := by
      rw [hQ1def, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_one,
        Polynomial.eval_X, hcast]
    have hevL1 : L1.eval (n : ℂ) = l.eval (-((n - 1 : ℕ) : ℂ)) := by
      rw [hL1def, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_one,
        Polynomial.eval_X, hcast]
    -- the two row relations (at `n` and `n-1`)
    have hreln := hM n (by omega)
    have hreln1 := hM (n - 1) (by omega)
    have e1 : Q0.eval (n : ℂ) * V n = -L0.eval (n : ℂ) := by
      rw [hev0, hevL0]; linear_combination hreln
    have e2 : Q1.eval (n : ℂ) * V (n - 1) = -L1.eval (n : ℂ) := by
      rw [hev1, hevL1]; linear_combination hreln1
    have hd := hdiff n hn1
    -- expand `D` and `num`, then combine
    simp only [hDdef, hdenomdef, hnumdef, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_neg]
    linear_combination (-(Q0.eval (n : ℂ) * Q1.eval (n : ℂ))) * hd
      + Q1.eval (n : ℂ) * e1 - Q0.eval (n : ℂ) * e2
  -- `num ≠ 0` (else `n^{-s} = 0`)
  have hnum : num ≠ 0 := by
    obtain ⟨n, hheqn, hDn, hn1⟩ :=
      (heq.and ((eventually_eval_ne_zero hDne).and (eventually_ge_atTop 1))).exists
    intro hc
    rw [hc, Polynomial.eval_zero] at hheqn
    have hnc : (n : ℂ) ≠ 0 := by
      have : (1 : ℕ) ≤ n := hn1
      exact_mod_cast Nat.one_le_iff_ne_zero.mp this
    have hcpow : (n : ℂ) ^ (-s) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hnc]; exact Complex.exp_ne_zero _
    exact hDn (by
      rcases mul_eq_zero.mp hheqn with h | h
      · exact absurd h hcpow
      · exact h)
  exact not_eventually_cpow_polyRatio hs hnum hDne heq

end HurwitzN2Survivor
